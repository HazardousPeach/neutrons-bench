module ControlFlow
where

import Control.Lens hiding ((^.), use, op)
import Control.Monad hiding (join)
import Control.Monad.State hiding (join)
import Data.List
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S

import qualified CalcExp as CE
import Multi
import qualified HL
import HL (letterToIndex, charToIndex, indexToLetter, indexToChar, idx,
    (^.), use, HlRecordType(..))
import Record
import ToExtraction2
import qualified Query2 as Q

import Debug.Trace


makeEdge nameMap recName rl = [(recName, nameMap M.! fromIntegral rl)]

opcodeEdges nameMap recName (Q.MProcess rl) = makeEdge nameMap recName rl
opcodeEdges nameMap recName (Q.MHavocProcess rl) = makeEdge nameMap recName rl
opcodeEdges nameMap recName (Q.MCalcCond _ _ _ ops) =
    concatMap (opcodeEdges nameMap recName) ops
opcodeEdges nameMap recName (Q.MScheduleCallback _ ops) =
    --[(recName, recName ++ "$cb")] ++
    concatMap (opcodeEdges nameMap (recName ++ "$cb")) ops
opcodeEdges _ _ _ = []

recordEdges nameMap rn (Q.RecordProgram _ ops) =
    let recName = nameMap M.! fromIntegral rn
    in concatMap (opcodeEdges nameMap recName) ops

databaseEdges :: HL.HlDatabase -> [(String, String)]
databaseEdges hldb =
    let nameMap = hldbNameMap hldb
        (dbp, _) = compile hldb
    in concat $ zipWith (recordEdges nameMap) [0..] dbp


opcodeDataEdges nameMap recName (Q.MReadLink fl _ _ _) =
    [(nameMap M.! fromIntegral (Q.fl_rn fl), recName)]
opcodeDataEdges nameMap recName (Q.MWriteLink _ _ fl _) =
    [(recName, nameMap M.! fromIntegral (Q.fl_rn fl))]
opcodeDataEdges nameMap recName (Q.MHavocWrite fl _) =
    [(recName, nameMap M.! fromIntegral (Q.fl_rn fl))]
opcodeDataEdges nameMap recName (Q.MCalcCond _ _ _ ops) =
    concatMap (opcodeDataEdges nameMap recName) ops
opcodeDataEdges nameMap recName (Q.MScheduleCallback _ ops) =
    concatMap (opcodeDataEdges nameMap (recName ++ "$cb")) ops
opcodeDataEdges _ _ _ = []

recordDataEdges nameMap rn (Q.RecordProgram _ ops) =
    let recName = nameMap M.! fromIntegral rn
    in concatMap (opcodeDataEdges nameMap recName) ops

databaseDataEdges :: HL.HlDatabase -> [(String, String)]
databaseDataEdges hldb =
    let nameMap = hldbNameMap hldb
        (dbp, _) = compile hldb
    in concat $ zipWith (recordDataEdges nameMap) [0..] dbp


findNonPassive :: HL.HlDatabase -> S.Set String
findNonPassive hldb =
    S.fromList $ map fst $
        filter (\(_,r) -> r ^. HL.hlr_SCAN /= HL.Scan_Passive) $
        M.toList hldb


walkGraph :: M.Map String [String] -> S.Set String -> S.Set String
walkGraph g cur =
    let add = S.fromList $ concatMap (\n -> fromMaybe [] $ M.lookup n g) $ S.toList cur
        next = S.union cur add
    in if next == cur then cur else walkGraph g next


genGraph hldb targets =
    let targetSet = S.fromList targets
        allEdges = databaseEdges hldb
        allDataEdges = databaseDataEdges hldb

        gFwd = M.fromListWith (++) $ map (\(n1, n2) -> (n1, [n2])) allEdges
        downstream = walkGraph gFwd targetSet
        gRev = M.fromListWith (++) $ map (\(n1, n2) -> (n2, [n1])) allEdges
        upstream = walkGraph gRev targetSet

        scc = S.intersection upstream downstream

        internalEdges = filter
            (\(n1, n2) -> S.member n1 scc && S.member n2 scc) allEdges
        sources = M.fromListWith (++) $ map (\(n1, n2) -> (n2, [n1])) $ filter
            (\(n1, n2) -> not (S.member n1 scc) && S.member n2 scc) allEdges
        sinks = M.fromListWith (++) $ map (\(n1, n2) -> (n1, [n2])) $ filter
            (\(n1, n2) -> S.member n1 scc && not (S.member n2 scc)) allEdges

        -- For each record in `scc`, a set of records that are upstream of its
        -- sources / downstream of its sinks.
        sourceUpstream = M.map (walkGraph gRev . S.fromList) sources
        sourceUpstreamRev = M.fromListWith (++) $
            concatMap (\(k,v) -> S.toList v >>= \v' -> [(v', [k])]) $
            M.toList sourceUpstream
        sinkDownstream = M.map (walkGraph gFwd . S.fromList) sinks
        sinkDownstreamRev = M.fromListWith (++) $
            concatMap (\(k,v) -> S.toList v >>= \v' -> [(v', [k])]) $
            M.toList sinkDownstream

        internalDataEdges = filter
            (\(n1, n2) -> S.member n1 scc && S.member n2 scc) allDataEdges
        dataToSources = concatMap
            (\(n1, n2) -> do
                guard $ S.member n1 scc
                n2' <- fromMaybe [] (M.lookup n2 sourceUpstreamRev)
                return (n1, n2')) allDataEdges
        dataToSinks = concatMap
            (\(n1, n2) -> do
                guard $ S.member n1 scc
                n2' <- fromMaybe [] (M.lookup n2 sinkDownstreamRev)
                return (n1, n2')) allDataEdges

    in traceShow ("down", downstream) $ traceShow ("up", upstream) $ unlines $
        ["digraph {"
        ,"node [shape=plaintext];"
        ,"edge [len=3];"
        ] ++
        map (\rn -> show rn ++ "[shape=box];") (S.toList scc) ++
        map (\(n1, n2) -> show n1 ++ "->" ++ show n2 ++ ";") internalEdges ++

        map (\(n1, n2) -> show n1 ++ "->" ++ show n2 ++ " [color=darkgreen,w=0.3];") internalDataEdges ++
        map (\(n1, n2) -> show n1 ++ "->" ++ show (n2 ++ "$sinks") ++ " [color=darkgreen,w=0.3];") dataToSinks ++
        map (\(n1, n2) -> show n1 ++ "->" ++ show (n2 ++ "$sources") ++ " [color=darkred,w=0.3];") dataToSources ++

        map (\n ->
            let ss = fromMaybe [] $ M.lookup n sources
                ss' = fromMaybe [] $ liftM S.toList $ M.lookup n sourceUpstream
                label1 = show (length ss) ++ " sources"
                label2 = show (length ss') ++ " upstream"
                label =
                    if null ss then Nothing
                    else if null ss' then Just $ "(" ++ label1 ++ ")"
                    else Just $ "(" ++ label1 ++ ", " ++ label2 ++ ")"
            in case label of
                Just label ->
                    show (n ++ "$sources") ++ " [label=" ++ show label ++ "]; " ++
                    show (n ++ "$sources") ++ "->" ++ show n ++ ";"
                Nothing -> ""
            ) (S.toList scc) ++

        map (\n ->
            let ss = fromMaybe [] $ M.lookup n sinks
                ss' = fromMaybe [] $ liftM S.toList $ M.lookup n sinkDownstream
                label1 = show (length ss) ++ " sinks"
                label2 = show (length ss') ++ " downstream"
                label =
                    if null ss then Nothing
                    else if null ss' then Just $ "(" ++ label1 ++ ")"
                    else Just $ "(" ++ label1 ++ ", " ++ label2 ++ ")"
            in case label of
                Just label ->
                    show (n ++ "$sinks") ++ " [label=" ++ show label ++ "]; " ++
                    show n ++ "->" ++ show (n ++ "$sinks") ++ ";"
                Nothing -> ""
            ) (S.toList scc) ++

            {-
        map (\(n, ss) ->
            let label = "(" ++ show (length ss) ++ " sinks)" in
            show (n ++ "$sources") ++ " [label=" ++ show label ++ "]; " ++
            show n ++ "->" ++ show (n ++ "$sources") ++ ";") (M.toList sinks) ++
            -}
        ["}"]


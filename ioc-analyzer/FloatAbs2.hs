{-# LANGUAGE CPP, TemplateHaskell, DataKinds, Rank2Types, FlexibleContexts #-}
module FloatAbs2
where

import Control.Lens hiding ((^.), use, op)
import Control.Monad hiding (join)
import Control.Monad.State hiding (join)
import Data.List
import qualified Data.Map as M
import Data.Maybe

import qualified CalcExp as CE
import Multi
import qualified HL
import HL (letterToIndex, charToIndex, indexToLetter, indexToChar, idx,
    (^.), use, HlRecordType(..))
import Record
import ToExtraction2
import qualified Query2 as Q

import Debug.Trace



changeList dba1 dba2 =
    catMaybes $ zipWith3 (\idx ra1 ra2 ->
        if ra1 /= ra2 then Just idx else Nothing) [0..] dba1 dba2


updateAbs dbp dba =
    fromMaybe (error $ "float_abs_update failed") (Q.float_abs_update dbp dba)

truncAbs dba1 dba2 =
    fromMaybe (error $ "float_abs_truncate failed") (Q.float_abs_truncate dba1 dba2)

runToFixedPoint dbp dba =
    let go lastNumChanges counter dba =
            let dba' = updateAbs dbp dba
                cl = changeList dba dba'
            in traceShow ("changed", cl) $
                if null cl then dba'
                else if length cl == lastNumChanges then
                    if counter <= 0 then go lastNumChanges 3 (truncAbs dba dba')
                    else go lastNumChanges (counter - 1) dba'
                else go (length cl) 3 dba'
    in go 0 3 dba

analyze :: HL.HlDatabase -> [Override] -> Q.Database_abs
analyze hldb overrides =
    let (dbp, dbs) = compile hldb
        dba0 = Q.float_abs_init dbs
        dba1 = Q.float_abs_apply_overrides dba0 overrides
        dba = runToFixedPoint dbp dba1
    in case Q.float_abs_check dbp dba of
        Left _ -> dba
        Right e ->
            let nameMap = hldbNameMap hldb
            in error $ unlines $ "" : concatMap (reportAbsError nameMap) e

test hldb overrides =
    let (dbp, dbs) = compile hldb
        dba0 = Q.float_abs_init dbs
        dba1 = Q.float_abs_apply_overrides dba0 overrides
        dba = dba1
    in putStrLn $ showDatabase hldb dba


type Override = ((Q.Record_name, Q.Field_name), Q.Abs_value)

showValue :: Q.Abs_value -> String
showValue Nothing = "*"
showValue (Just (low, high))
  | low == high = show low
  | otherwise = show low ++ " .. " ++ show high

showFields :: Q.Record_abs -> [String]
showFields ra =
    let zeroFields = filter (\fn -> Q.float_abs_read_field ra fn == Just (Just (0, 0))) allFields
        starFields = filter (\fn -> Q.float_abs_read_field ra fn == Just Nothing) allFields
        lns = mapMaybe (\fn -> do
            val <- Q.float_abs_read_field ra fn
            guard $ val /= Just (0, 0) && val /= Nothing
            return $ "  " ++ drop 2 (show fn) ++ ": " ++ showValue val) allFields
        maybeLine label fns = if null fns then []
            else ["  " ++ intercalate ", " (map (drop 2 . show) fns) ++ ": " ++ label]
    in lns ++ maybeLine "0" zeroFields ++ maybeLine "*" starFields

showDatabase :: HL.HlDatabase -> Q.Database_abs -> String
showDatabase hldb dba =
    let names = M.keys hldb
        blocks = zipWith (\name ra ->
            let ty = drop 2 $ show $ Q.record_abs_type ra
            in "" : (ty ++ "  " ++ name ++ ":") : showFields ra) names dba
    in unlines $ concat blocks


parseOverrideLine :: HL.HlDatabase -> [String] -> [Override]
parseOverrideLine _ [] = []
parseOverrideLine _ (('#' : _) : _) = []
parseOverrideLine hldb ln@(recName : fieldName : range) =
    let nameToId = hldbNameToId hldb
        absValue = case range of
                       ["*"] -> Nothing
                       [low, high] -> Just (read low, read high)
                       _ -> error $ "invalid override line: " ++ show ln
        rns = case recName of
                  '@' : asgName -> [nameToId M.! name |
                                    (name, rec) <- M.toList hldb,
                                    rec ^. HL.hlr_ASG == asgName]
                  name -> [nameToId M.! recName]
        fns = case fieldName of
                  "*" -> allFields
                  fn -> [conv fieldName]
    in [((rn, fn), absValue) | rn <- rns, fn <- fns]

parseOverrides :: HL.HlDatabase -> String -> [Override]
parseOverrides hldb s = concatMap (parseOverrideLine hldb . words) $ lines s

readOverrides hldb filename = readFile filename >>= return . parseOverrides hldb


printOverride hldb ((rn, fn), val) =
    let recName = hldbNameMap hldb M.! fromIntegral rn
        fieldName = drop 2 $ show fn
        valStr = showValue val
    in putStrLn $ recName ++ "." ++ fieldName ++ ": " ++ valStr

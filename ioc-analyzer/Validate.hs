module Validate
where

import Control.Lens hiding ((^.), use, op)
import Control.Monad hiding (join)
import Control.Monad.State hiding (join)
import Data.List
import qualified Data.Map as M
import Data.Maybe

import qualified CalcExp as CE
import Iocsh
import Multi
import qualified HL
import HL (letterToIndex, charToIndex, indexToLetter, indexToChar, idx,
    (^.), use, HlRecordType(..))
import Record
import ToExtraction2
import qualified Query2 as Q

import Debug.Trace


validate :: HL.HlDatabase -> [Command] -> Q.Trace -> (String, Int)
validate hldb cmds trace =
    let recNames = findDbtrs cmds
        q = zipWith (\i name -> (i * 1000, Q.IProcess $ hldbNameToId hldb M.! name))
                [0..] recNames
        (dbp, dbs) = compile hldb

        traceLines = zipWith (\i t -> "  " ++ show (length trace - i) ++ ": " ++ show t ++ "\n")
                [0..] trace
    in case Q.validate_trace_event_loop dbp dbs q trace of
        Left (dbs', oes) -> (showDatabase hldb dbs', 0)
        Right e -> ("trace:\n" ++ concat traceLines ++
                reportValidateError (hldbNameMap hldb) e,
                    validateErrorCode e)


findDbtrs cmds =
    mapMaybe (\cmd -> case cmd of
            FuncCmd "dbtr" args ->
                case args of
                    [recName] -> Just recName
                    _ -> error $ "unexpected args for dbtr: " ++ show args
            _ -> Nothing) cmds


showFields :: Q.Record_state -> [String]
showFields rs =
    mapMaybe (\fn -> do
        val <- Q.read_field rs fn
        return $ "  " ++ drop 2 (show fn) ++ ": " ++ show val) allFields

showDatabase :: HL.HlDatabase -> Q.Database_state -> String
showDatabase hldb dbs =
    let names = M.keys hldb
        blocks = zipWith (\name rs ->
            let ty = drop 2 $ show $ Q.record_state_type rs
            in "" : (ty ++ "  " ++ name ++ ":") : showFields rs) names dbs
    in unlines $ concat blocks


validateErrorCode e = case e of
    Q.TypeMismatch _ _ -> 20
    Q.ValueMismatch _ _ -> 21
    Q.RecordStateMismatch _ _ _ -> 22
    Q.ReadRecordFieldFailed _ _ -> 23
    Q.WriteRecordFieldFailed _ _ _ -> 24
    Q.InvalidExpr _ -> 25
    Q.SeekHitBoundary -> 26
    Q.EndOfTrace -> 27
    Q.EmptyStack -> 28
    Q.OutOfFuel -> 29
    Q.UnusedEvents _ -> 30
    Q.InRecord _ _ e -> validateErrorCode e
    Q.InOpcode _ e -> validateErrorCode e
    Q.WithRemainingTrace _ e -> validateErrorCode e
    Q.WithCallStack _ e -> validateErrorCode e
    Q.InPop _ e -> validateErrorCode e
    Q.InConversion _ _ e -> validateErrorCode e
    Q.OtherError _ -> 34
    Q.Impossible _ -> 99

reportValidateError nameMap e = case e of
    Q.TypeMismatch ty1 ty2 ->
        "type mismatch: got " ++ show ty1 ++ " but expected " ++ show ty2
    Q.ValueMismatch val1 val2 ->
        "value mismatch: got " ++ show val1 ++ " but expected " ++ show val2
    Q.RecordStateMismatch rn rs1 rs2 ->
        "record state mismatch: " ++ reportRecordName nameMap rn ++ ": " ++
            "\n  interp:  "  ++ show rs1 ++
            "\n  trace:   " ++ show rs2
    Q.ReadRecordFieldFailed rn fn ->
        "read_record_field(" ++ reportRecordName nameMap rn ++ ", " ++ show fn ++ ") failed"
    Q.WriteRecordFieldFailed rn fn ty ->
        "read_record_field(" ++ reportRecordName nameMap rn ++ ", " ++ show fn ++ ", "
        ++ show ty ++ ") failed"
    Q.InvalidExpr e -> "invalid expr"
    Q.SeekHitBoundary -> "seek hit record processing boundary"
    Q.EndOfTrace -> "unexpected end of trace"
    Q.EmptyStack -> "empty stack"
    Q.OutOfFuel -> "out of fuel"
    Q.UnusedEvents n -> "finished with " ++ show n ++ " trace events left over"

    Q.InRecord rt rn e' ->
        "in " ++ show rt ++ " record " ++ reportRecordName nameMap rn ++
        ": " ++ reportValidateError nameMap e'
    Q.InOpcode op e' ->
        "in opcode " ++ show op ++ ": " ++ reportValidateError nameMap e'
    Q.WithRemainingTrace n e' ->
        "with " ++ show n ++ " trace events remaining: " ++ reportValidateError nameMap e'
    Q.WithCallStack [] e' -> reportValidateError nameMap e'
    Q.WithCallStack rns e' ->
        "in " ++ intercalate " > " (map (reportRecordName nameMap) (reverse rns)) ++
        ": " ++ reportValidateError nameMap e'
    Q.InPop rn e' ->
        "while popping record " ++ reportRecordName nameMap rn ++
        ": " ++ reportValidateError nameMap e'
    Q.InConversion v ty e' ->
        "in conversion of " ++ show v ++ " from " ++ show (Q.value_type v) ++
        " to " ++ show ty ++ ": " ++ reportValidateError nameMap e'

    Q.OtherError msg -> conv msg
    Q.Impossible msg -> "BUG: " ++ conv msg


readTrace hldb filename = do
    s <- readFile filename
    return $ parseTrace hldb s

lineEvents :: String -> [String]
lineEvents s =
    let sFindStart [] = []
        sFindStart s =
            let s' = dropWhile (/= '[') s
                (delim, s'') = break (/= '[') s'
            in if length delim >= 2 then sFindEnd "" s'' else sFindStart s''
        sFindEnd acc s =
            let (inner, s') = break (== ']') s
                (delim, s'') = break (/= ']') s'
            in if length delim >= 2
                then (acc ++ inner) : sFindStart s''
                else sFindEnd (acc ++ inner ++ delim) s''
    in sFindStart s

collectEvents s = unlines $ concatMap lineEvents $ lines s

parseTrace hldb s =
    let ls = map words $ concatMap lineEvents $ lines s
    in let (x, y) = runState (parseEvents (hldbNameToId hldb)) ls
    in trace ("remaining: " ++ show (length y)) x
    --in evalState (parseEvents (hldbNameToId hldb)) ls

-- `PROC` field is a UCHAR in epics-base, but semantics have it as TEnum
tryParseTypeAndValue "UCHAR" [val] = Just $ convEnumValue $ read val
tryParseTypeAndValue "USHORT" [val] = Just $ convEnumValue $ read val
tryParseTypeAndValue "ENUM" [val] = Just $ convEnumValue $ read val
tryParseTypeAndValue "MENU" [val] = Just $ convEnumValue $ read val
tryParseTypeAndValue "LONG" [val] = Just $ convLongValue $ read val
tryParseTypeAndValue "DOUBLE" [val] =
    Just $ Q.VDouble $ (conv :: Double -> Q.E_double) $ read $
        case val of
            "inf" -> "Infinity"
            "-inf" -> "-Infinity"
            "nan" -> "NaN"
            "-nan" -> "-NaN"
            _ -> val
tryParseTypeAndValue "STRING" val =
    Just $ Q.VString $ (conv :: String -> Q.E_string) $
        takeWhile (/= '\0') $ map (toEnum . read) val
tryParseTypeAndValue _ _ = Nothing

parseTypeAndValue ty val = fromMaybe
    (error ("trace error: unsupported field type: " ++ ty)) $
    tryParseTypeAndValue ty val

isEmpty :: State [[String]] Bool
isEmpty = do
    ls <- get
    trace ("isEmpty? " ++ show (length ls) ++ " remain") $ return $ null ls

takeLine :: State [[String]] [String]
takeLine = do
    ls <- get
    let (l, ls') = case ls of
                [] -> error "unexpected end of trace"
                l : ls' -> (l, ls')
    put ls'
    return l

parseEvent :: M.Map String Integer -> State [[String]] [Q.Trace_event]
parseEvent invNameMap = takeLine >>= \l -> case l of
    ("error" : msg) -> trace ("trace error: " ++ unwords msg) $ return []
    ("dbGetLinkValue" : ty : val) ->
        return [Q.DbGetLinkValue $ parseTypeAndValue ty val]
    ("dbPutLinkValue" : ty : val) ->
        return [Q.DbPutLinkValue $ parseTypeAndValue ty val]
    ["dbTraceRecordState", recName, recTy, "BEGIN", kind] -> do
        recState <- parseRecordState recName recTy
        case kind of
            "BEFORE_PROCESS" -> return [Q.RecordBegin (invNameMap M.! recName) recState]
            "AFTER_PROCESS" -> return [Q.RecordEnd (invNameMap M.! recName) recState]
            "PACT_NO_PROCESS" -> return
                    [ Q.RecordBegin (invNameMap M.! recName) recState
                    , Q.RecordEnd (invNameMap M.! recName) recState ]
            "SCALC_PERFORM" -> return [Q.StrCalcResult recState]
    (first : _) -> trace ("unknown entry in trace: " ++ first) $ return []

parseEvents :: M.Map String Integer -> State [[String]] [Q.Trace_event]
parseEvents invNameMap = do
    done <- isEmpty
    if done then return [] else do
        e <- parseEvent invNameMap
        es <- parseEvents invNameMap
        return $ e ++ es

recordTypeByName :: String -> Q.Record_type
recordTypeByName tyName = case tyName of
    "calc" -> Q.RtCalc
    "calcout" -> Q.RtCalcOut
    "scalcout" -> Q.RtStrCalcOut
    -- NYI - parameterized types need additional info from the instrumentation
    "acalcout" -> error $ "recordTypeByName: acalcout type not supported"
    "fanout" -> Q.RtFanout
    "dfanout" -> Q.RtDFanout
    "seq" -> Q.RtSeq
    "ai" -> Q.RtAnalogIn
    "ao" -> Q.RtAnalogOut
    "bi" -> Q.RtBinaryIn
    "bo" -> Q.RtBinaryOut
    "mbbo" -> Q.RtMBBO
    "stringin" -> Q.RtStringIn
    "stringout" -> Q.RtStringOut
    "longin" -> Q.RtLongIn
    "longout" -> Q.RtLongOut
    "waveform" -> error $ "recordTypeByName: waveform type not supported"
    "subArray" -> error $ "recordTypeByName: subArray type not supported"
    "asyn" -> Q.RtAsyn
    _ -> error $ "recordTypeByName: unknown type " ++ show tyName

trySetField rs fnStr rawTyStr valStrs =
    let withErr m e = case m of
            Just x -> Right x
            Nothing -> Left e
        result = do
            val <- withErr (tryParseTypeAndValue rawTyStr valStrs)
                ("failed to parse " ++ show valStrs ++ " as " ++ rawTyStr)
            fn <- withErr (ToExtraction2.fieldByName fnStr)
                ("failed to parse field name " ++ show fnStr)
            rs' <- withErr (Q.write_field rs fn val)
                ("failed to write " ++ show val ++ " to " ++ show fn)
            return rs'
    in case result of
            Left e -> trace e rs
            Right rs' -> rs'

parseRecordState :: String -> String -> State [[String]] Q.Record_state
parseRecordState recName tyName =
    let go r = do
            l <- takeLine
            case l of
                ["dbTraceRecordState", recName', "END", kind] | recName' == recName -> return r
                ("dbTraceRecordState" : recName' : "FIELD" : fieldName : fty : valStr)
                  | recName' == recName -> go $ trySetField r fieldName fty valStr
                _ -> error $ "failed to parse line " ++ show l ++ " for record " ++ show recName
    in go $ Q.default_record $ recordTypeByName tyName

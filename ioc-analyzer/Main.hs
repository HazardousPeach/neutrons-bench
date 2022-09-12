{-# LANGUAGE CPP #-}

import Control.Applicative ((<$>))
import Control.Exception (evaluate)
import Control.Monad
import Data.Char (toLower)
import Data.List (intercalate, sort)
import qualified Data.Map as M
import Data.Maybe (catMaybes)
import System.Environment
import System.Exit
import Text.Parsec hiding (label, State)

import Lexer
import Parser
import Record
import ExpParser
import Substs
import Iocsh
import Lint
import ToRosette
import CheckAsyn
import CmdGen(genCmdFile)
import CycleCheck
import ToCoq
import FieldInfo
import HL

#ifndef NO_COQ
import ToExtraction
import qualified ToExtraction2
import ToC
import FloatAbs
import qualified FloatAbs2
import qualified ControlFlow
import qualified Validate
#endif

import Debug.Trace

main = do
    args <- getArgs
    let action = case args of
            ["summarize"] -> const $ mapM_ (putStrLn . printRecord)
            ["print-records"] -> const $ mapM_ (putStrLn . printRecord)
            ["print-input-links"] -> const $ printLinks . inputLinks
            ["print-output-links"] -> const $ printLinks . outputLinks
            ["lint", exceptionsFile] -> const $ \db -> do
                exceptions <- readFile exceptionsFile >>= (return . parseRecordNames)
                let warnings = lint (LintContext exceptions) db
                mapM_ print warnings
                if all lintWarningOk warnings then exitWith ExitSuccess else exitWith $ ExitFailure 1
            ["to-rosette"] -> const $ putStrLn . toRosette
            ["gen-cmd-file", seedString] ->
                let seed = (read seedString :: Integer) in
                const $ \db -> do
                    cmds <- genCmdFile seed db
                    putStrLn cmds
            ["parse-exp", e] -> const $ const $ print $ parseExp e
            ["check-relay-writes", pvName, arrIndex, relayNumber] ->
                checkRelayWrites pvName (read arrIndex) (read relayNumber)
            ["to-sqlite"] -> const $ \db -> do
                putStrLn "CREATE TABLE records(name STRING PRIMARY KEY, type STRING);"
                putStrLn "CREATE TABLE aliases(record_name STRING PRIMARY KEY, alias STRING);"
                putStrLn "CREATE TABLE fields(record_name STRING, field_name STRING, value STRING);"
                mapM_ (\(Record { r_name = [Literal name], r_type = ty, r_fields = fields, r_aliases = aliases }) -> do
                    putStrLn $ "INSERT OR IGNORE INTO records (name, type) VALUES (" ++ show name ++ ", " ++ show (substStringToStr ty) ++ ");"
                    mapM_ (\rn -> putStrLn $ "INSERT OR IGNORE INTO aliases (record_name, alias) VALUES (" ++ show name ++ ", " ++ show (recordNameToStr rn) ++ ");") aliases
                    mapM_ (\(field, [Literal val]) -> putStrLn $ "INSERT OR IGNORE INTO fields (record_name, field_name, value) VALUES (" ++ show name ++ ", " ++ show field ++ ", " ++ show val ++ ");") fields) db
#ifndef NO_COQ
            ["run-extraction"] -> \cmds db ->
                let (hldb, errs) = parseDatabase db
                in runExtraction cmds hldb
            ["to-c"] -> const $ toC
            ["analyze-floats"] -> const $ \db -> do
                let (hldb, errs) = parseDatabaseWithFallback db
                    hldb' = fixHavoc $ fixMissingRecords $ hldb
                print $ FloatAbs.makeAbsDatabase hldb
                let adb = FloatAbs.runAnalysis hldb
                print adb
                forM_ (sort $ report adb) $ print
                --forM_ (M.toList adb) $ print
#endif
            ["to-coq"] -> const $ toCoq
            ["dump-clean"] -> const $ mapM_ (putStrLn . printCleanRecord)
            ["find-cycles"] -> \_cmds db -> do
                let cycles = findCycles db
                mapM_ print cycles
            ["control-graph"] -> \_cmds db -> do
                let edges = getEdges db
                putStrLn "digraph {"
                forM_ edges $ \(s, t) ->
                    putStrLn $ show s ++ " -> " ++ show t ++ ";"
                putStrLn "}"
            ["list-link-targets", mode] -> \_cmds db -> do
                let linkTy = case mode of
                        "inlink" -> INLINK
                        "outlink" -> OUTLINK
                forM_ (collectLinkTargets db linkTy) $ \(rt, fn) ->
                    putStrLn $ rt ++ "." ++ fn
            ["test-hl"] -> const $ \db -> do
                forM_ db $ \r -> do
                    case parseRecord r of
                        Err e -> print ("error", e)
                        HL.Ok (HlRecord { _detail = HL.Havoc {} }) -> print ("success", "havoc")
                        HL.Ok r' -> print ("success", r_type r)
                        TryNext -> print ("error", "TryNext")
            ["test-hl2"] -> const $ \db -> do
                let hldb = fst $ parseDatabaseWithFallback db
                let hldb' = fixHavoc $ fixMissingRecords $ hldb
                forM_ (M.toList hldb') $ \(k,v) -> do
                    print k
                    print v

#ifndef NO_COQ
            ["typecheck"] -> const $ \db -> do
                let (hldb, errs) = parseDatabase db
                print errs
                print $ ToExtraction2.typecheckProgram hldb

            ["cycle-check"] -> const $ \db -> do
                let (hldb, errs) = parseDatabase db
                print $ ToExtraction2.cycleCheckHl hldb

            ("control-flow-graph" : names) -> const $ \db -> do
                let (hldb, errs) = parseDatabase db
                putStrLn $ ControlFlow.genGraph hldb names

            ("analyze-floats2" : args) -> const $ \db -> do
                let (hldb, errs) = parseDatabaseWithFallback db
                overrides <- case args of
                    [] -> return []
                    [overrideFile] -> FloatAbs2.readOverrides hldb overrideFile
                    _ -> error $ "bad args to analyze-floats2: " ++ show args
                --mapM_ (FloatAbs2.printOverride hldb) overrides
                let dba = FloatAbs2.analyze hldb overrides
                --FloatAbs2.test hldb overrides
                putStrLn $ FloatAbs2.showDatabase hldb dba

            ["list-trace-events", traceFile] -> \_cmds _db -> do
                s <- readFile traceFile
                putStrLn $ Validate.collectEvents s

            ["validate-trace", traceFile] -> \cmds db -> do
                let (hldb, errs) = parseDatabase db
                trace <- Validate.readTrace hldb traceFile
                forM_ trace $ \evt -> print evt
                let (msg, code) = Validate.validate hldb cmds trace
                putStrLn msg
                when (code /= 0) $ exitWith (ExitFailure code)
#endif

            _ -> error $ "bad command line arguments: " ++ show args
    evaluate action

    cmds <- parseContents command
    rss <- forM cmds $ \cmd -> case cmd of
        FuncCmd "dbLoadRecords" [filename] -> loadRecords filename ""
        FuncCmd "dbLoadRecords" [filename, substsStr] -> loadRecords filename substsStr
        FuncCmd "dbLoadTemplate" [filename] -> loadTemplate filename ""
        FuncCmd "dbLoadTemplate" [filename, substsStr] -> loadTemplate filename substsStr
        NoCmd -> return []
        _ -> trace ("ignored command: " ++ show cmd) $ return []
    let rs = concat rss

    action cmds rs
  where
    printLinks = mapM_ print . concatMap (\(n,k,v) -> let v' = parseFieldLink v in case v' of { (FieldLink _ _ _ _) -> [(n, k, v')]; _ -> [] } )

printCleanRecord :: Record -> String
printCleanRecord r =
    "record(" ++ substStringToStr (r_type r) ++ ", " ++ show (recordNameToStr $ r_name r) ++ ") {\n" ++
    concatMap (\rn -> "  alias(" ++ show (recordNameToStr rn) ++ ")\n") (r_aliases r) ++
    concatMap (uncurry printCleanField) (r_fields r) ++
    "}"

printCleanField :: FieldName -> SubstString -> String
--printCleanField f@"SCAN" [Literal v@"Passive"] = "  field(" ++ f ++ ", " ++ show v ++ ")\n"
printCleanField f@"SCAN" _ = "  field(" ++ f ++ ", \"Passive\")\n"
printCleanField f [Literal v] = "  field(" ++ f ++ ", " ++ show v ++ ")\n"

parseRecordNames :: String -> [RecordName]
parseRecordNames = catMaybes . map helper . lines
    where
        helper "" = Nothing
        helper ('#' : _) = Nothing
        helper s = Just [Literal s]

lintWarningOk (MissingCAAnnotation _ _ _) = True
lintWarningOk _ = False

printUsage records = do
    forM records $ \r -> do
        putStrLn $ substStringToStr (r_type r)
        forM (r_fields r) $ \(k,v) -> do
            putStrLn $ substStringToStr (r_type r) ++ "." ++ k

typeNameMap = M.fromList
    [ ("calc", "Calc")
    , ("calcout", "CalcOut")
    ]

toPython r | Just ty <- M.lookup (substStringToStr (r_type r)) typeNameMap =
    "db.register(" ++ show name ++ ", " ++ ty ++ "(" ++ intercalate ", " args ++ "))"
  where name = unwrapLiteral $ r_name r
        args = map (\(i,ss) -> map toLower i ++ "=" ++ show (unwrapLiteral ss)) (r_fields r)
toPython r = "db.register(" ++ show (unwrapLiteral $ r_name r) ++ ", DummyRecord())"

unwrapLiteral [] = ""
unwrapLiteral [Literal s] = s
unwrapLiteral _ = error $ "unwrapLiteral: not a list of zero or one literals"

collectLinkTargets db linkTy = do
    let dbMap = M.fromList [(unwrapLiteral $ r_name r, r) | r <- db]
    r <- db
    let r_ty = unwrapLiteral $ r_type r
    Just f_tys <- [M.lookup r_ty fieldtypes]
    (fn, fv) <- r_fields r
    Just f_ty <- [M.lookup fn f_tys]
    guard $ f_ty == linkTy
    FieldLink { fl_record = lr, fl_field = lf } <- [parseFieldLink $ unwrapLiteral fv]

    Just targetRecord <- [M.lookup lr dbMap]
    let tr_ty = unwrapLiteral $ r_type targetRecord
    return (tr_ty, lf)



loadRecords filename substsStr = do
    {-traceShow ("loading records", filename, substsStr) $ return ()-}
    records <- parseFile record filename
    let tokens = alexScanTokens substsStr
        substMap = M.fromList $
            case parse loadRecordSubsts filename tokens of
                Left err -> error $ show err
                Right x -> x
    return $ subVars (flip M.lookup substMap) records

loadTemplate filename substsStr = do
    {-traceShow ("loading template", filename) $ return ()-}
    substs <- parseFile substs filename
    let tokens = alexScanTokens substsStr
        substMap = M.fromList $
            case parse loadRecordSubsts filename tokens of
                Left err -> error $ show err
                Right x -> x
    let substs' = map (extendSubst substMap) substs
    concat <$> mapM evalSubsts substs'

extendSubst :: M.Map String String -> Substs -> Substs
extendSubst m s =
    let (vars, vals) = unzip (M.toList m) in
    s { s_vars = (s_vars s) ++ vars,
        s_values = map (++ vals) (s_values s) }

evalSubsts substs = do
    templateRecords <- parseFile record (s_file substs)
    return $ concatMap (\vs -> map (go vs) templateRecords) (s_values substs)
  where
    go values record = subVars (flip M.lookup varMap) record
      where varMap = M.fromList $ zip (s_vars substs) values



parseContents p = parseInput p <$> getContents

parseInput p = parseInput' p "<input>"

parseInput' p filename text =
    let tokens = alexScanTokens text
        items = case parse (do ss (); x <- many p; eof; return x) filename tokens of
            Left err -> error $ show err
            Right x -> x
    in items

parseFile p f = do
    {-traceShow ("parsing file", f) $ return ()-}
    result <- parseInput' p f <$> readFile f
    evaluate result

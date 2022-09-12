module ToCoq
where

import Control.Applicative ((<$>))
import Control.Monad
import Control.Monad.State
import Data.Bits
import Data.Char
import Data.Fixed
import qualified Data.Map as M
import Data.Maybe
import Data.Word
import Text.PrettyPrint.HughesPJ
import Unsafe.Coerce

import ExpParser
import Parser (StringPart(Literal), substStringToStr)
import Record


parseExpOrFail s =
  case parseExp s of
    Left err -> error (show err)
    Right e -> e

fieldLetter i = toEnum $ fromEnum 'A' + i


-- Pretty printer helper definitions

colonEq = text ":="
dot = text "."
lrecord = text "{|"
rrecord = text "|}"
blank = text ""

mkIndex i = text $ "$(mk_index " ++ show i ++ ")$"

idIndex i = text $ "idx" ++ show i
idFieldA2L i = text $ "f_" ++ [fieldLetter i]
idEvar i = text $ "EVar" ++ [fieldLetter i]
idEvar' c = text $ "EVar" ++ [c]
idRec n = text $ "REC_" ++ n
idField n = text $ "f_" ++ n

requireImport m = text "Require Import" <+> text m <> dot

definition name ty val =
    longDefStart name ty <+> val <> dot

longDefStart name ty =
    hsep [text "Definition", name, colon, ty, colonEq]

assign ident val = hsep [text ident, colonEq, val]


-- Value pretty printing functions

convPp NoProcessPassive = text "NPP"
convPp ProcessPassive = text "PP"

convDouble s = convDouble' $ read s

convDouble' :: Double -> Doc
convDouble' d =
    let w = unsafeCoerce d :: Word64
    in text "Z2B64" <+> integer (fromIntegral w)

convOptInLink s = case parseFieldLink s of
    NoLink -> text "None"
    FieldLink rn fn pp ms ->
        let ilRn = assign "il_rn" (idRec rn)
            ilFn = assign "il_fn" (idField fn)
            ilPp = assign "il_pp" (convPp pp)
        in text "Some" <+> lrecord <+> hsep (punctuate semi [ilRn, ilFn, ilPp]) <+> rrecord
    _ -> error $ "bad input link: " ++ show s

convOptOutLink s = case parseFieldLink s of
    NoLink -> text "None"
    FieldLink rn fn pp ms ->
        let olRn = assign "ol_rn" (idRec rn)
            olFn = assign "ol_fn" (idField fn)
            olPp = assign "ol_pp" (convPp pp)
        in text "Some" <+> lrecord <+> hsep (punctuate semi [olRn, olFn, olPp]) <+> rrecord
    _ -> error $ "bad output link: " ++ show s

convOptFwdLink "" = text "None"
convOptFwdLink s = text "Some" <+> lrecord <+> assign "fl_rn" (idRec s) <+> rrecord

convOOpt "Every Time" = text "EveryTime"
convOOpt "On Change" = text "OnChange"
convOOpt "When Zero" = text "WhenZero"
convOOpt "When Non-zero" = text "WhenNonzero"
convOOpt "Transition To Zero" = text "TransitionToZero"
convOOpt "Transition To Non-zero" = text "TransitionToNonzero"

convDOpt "Use CALC" = text "UseCalc"
convDOpt "Use OCAL" = text "UseOcal"

convCalc s = text "denote_expr_double" <+> parens (convExpr $ parseExpOrFail s)

convExpr :: Exp -> Doc
convExpr e = case e of
    EName [c] | c >= 'A' && c <= 'L' -> idEvar' c
    EVal v -> text "EConst" <+> parens (convDouble' v)
    EUnaryOp op x ->
        let op_doc =
                case op of
                Not -> text "UNot"
                Neg -> text "UNeg"
                _ -> error $ "unsupported unary op: " ++ show op
        in hsep [text "EUnaryOp", op_doc, parens (convExpr x)]
    EBinOp op x y ->
        let op_doc =
                case op of
                Plus -> text "BAdd"
                Times -> text "BMul"
                Minus -> text "BSub"
                Div -> text "BDiv"
                Eq -> text "BEq"
                Ne -> text "BNe"
                Gt -> text "BGt"
                Ge -> text "BGe"
                Lt -> text "BLt"
                Le -> text "BLe"
                And -> text "BAnd"
                Or -> text "BOr"
        in hsep [text "EBinaryOp", op_doc, parens (convExpr x), parens (convExpr y)]
    ECond c x y -> text "ECond" <+> hsep (map (parens . convExpr) [c, x, y])
    EAssign [c] x | c >= 'A' && c <= 'L' ->
        text "EAssign" <+> idEvar' c <+> parens (convExpr x)
    ESeq x y -> text "ESeq" <+> hsep (map (parens . convExpr) [x, y])


-- Top-level file parts

header = vcat $
    [ requireImport "List"
    , text "Import ListNotations."
    , requireImport "ZArith"
    , requireImport "Epics"
    , requireImport "EpicsAux"
    , requireImport "Expr"
    , requireImport "Multi"
    , requireImport "FloatAux"
    , blank
    ] ++
    [ definition (idIndex i) (text "index 12") (mkIndex i) $$
      definition (idFieldA2L i) (text "field_name") (text "f_A_to_L" <+> idIndex i) $$
      definition (idEvar i) (text "expr e_double 12") (text "EVar" <+> idIndex i)
      | i <- [0 .. 11] ]

recordNames db = vcat [recordName r i | (r, i) <- zip db [0..]]
recordName r i = case r_name r of
    [Literal n] -> definition (idRec n) (text "record_name") (int i)
    _ -> error $ "expected [Literal _] for r_name"

recordConfigs db = 
    longDefStart (text "my_dbc") (text "database_config") <+> lbrack $$
    (nest 4 $ vcat $ punctuate semi $ map recordConfig db) $$
    rbrack <> dot

recordStates db = 
    longDefStart (text "my_dbs") (text "database_state") <+> lbrack $$
    (nest 4 $ vcat $ punctuate semi $ map recordState db) $$
    rbrack <> dot


-- Record type info

type FieldPrinter = (M.Map String String -> [(String, Doc)])

data RecordInfo = RecordInfo String String FieldPrinter FieldPrinter

allRecords =
    [ RecordInfo "calc" "Calc"          ppCalcConfig        ppCalcState
    , RecordInfo "calcout" "CalcOut"    ppCalcOutConfig     ppCalcOutState
    , RecordInfo "fanout" "Fanout"      ppFanoutConfig      ppFanoutState
    , RecordInfo "ai" "AnalogIn"        ppAnalogInConfig    ppAnalogInState
    , RecordInfo "ao" "AnalogOut"       ppAnalogOutConfig   ppAnalogOutState
    , RecordInfo "bi" "BinaryIn"        ppBinaryInConfig    ppBinaryInState
    , RecordInfo "bo" "BinaryOut"       ppBinaryOutConfig   ppBinaryOutState
    ]

takeField fm fn def conv = conv $ fromMaybe def (M.lookup fn fm)

ppCalcConfig fm =
    [ ("INPA_to_INPL", parens $ vcat $ punctuate comma $
            map (\k -> takeField fm ("INP" ++ [k]) "" convOptInLink) ['A' .. 'L'])
    , ("FLNK", takeField fm "FLNK" "" convOptFwdLink)
    , ("CALC", takeField fm "CALC" "0" convCalc)
    ]
ppCalcState fm =
    [ ("A_to_L", parens $ vcat $ punctuate comma $
            map (\k -> takeField fm [k] "0" convDouble) ['A' .. 'L'])
    , ("VAL", takeField fm "VAL" "0" convDouble)
    ]

ppCalcOutConfig fm =
    [ ("INPA_to_INPL", parens $ vcat $ punctuate comma $
            map (\k -> takeField fm ("INP" ++ [k]) "" convOptInLink) ['A' .. 'L'])
    , ("FLNK", takeField fm "FLNK" "" convOptFwdLink)
    , ("CALC", takeField fm "CALC" "0" convCalc)
    , ("OCAL", takeField fm "OCAL" "0" convCalc)
    , ("OOPT", takeField fm "OOPT" "0" convOOpt)
    , ("DOPT", takeField fm "DOPT" "0" convDOpt)
    ]
ppCalcOutState fm =
    [ ("A_to_L", parens $ vcat $ punctuate comma $
            map (\k -> takeField fm [k] "0" convDouble) ['A' .. 'L'])
    , ("VAL", takeField fm "VAL" "0" convDouble)
    , ("OVAL", takeField fm "OVAL" "0" convDouble)
    ]

ppFanoutConfig fm =
    [ ("LNK1_to_LNK6", parens $ vcat $ punctuate comma $
            map (\k -> takeField fm ("LNK" ++ [k]) "" convOptFwdLink) ['1' .. '6'])
    ]
ppFanoutState fm = []

ppAnalogInConfig fm =
    [ ("FLNK", takeField fm "FLNK" "" convOptFwdLink) ]
ppAnalogInState fm =
    [ ("VAL", takeField fm "VAL" "0" convDouble) ]

ppAnalogOutConfig fm = undefined
    [ ("DOL", takeField fm "DOL" "" convOptInLink)
    , ("FLNK", takeField fm "FLNK" "" convOptFwdLink)
    ]
ppAnalogOutState fm = []

ppBinaryInConfig fm = undefined
ppBinaryInState fm = undefined

ppBinaryOutConfig fm = undefined
ppBinaryOutState fm = undefined


-- Misc

lower s = tail $ concatMap (\c -> if isUpper c then '_' : [toLower c] else [c]) s

capitalNameMap = M.fromList
    [(eName, capName) | RecordInfo eName capName _ _ <- allRecords]
lowerNameMap = M.map (\s -> lower s) capitalNameMap
ppConfigMap = M.fromList
    [(eName, ppConfig) | RecordInfo eName _ ppConfig _ <- allRecords]
ppStateMap = M.fromList
    [(eName, ppState) | RecordInfo eName _ _ ppState <- allRecords]

configCtor r = text $ "Rc" ++ capitalNameMap M.! (substStringToStr $ r_type r)
stateCtor r = text $ "Rs" ++ capitalNameMap M.! (substStringToStr $ r_type r)

recordConfig r =
    configCtor r <+> lrecord $$
    (nest 4 $ vcat $ punctuate semi $ ppConfig (substStringToStr $ r_type r) (r_fields r)) $$
    rrecord

recordState r =
    stateCtor r <+> lrecord $$
    (nest 4 $ vcat $ punctuate semi $ ppState (substStringToStr $ r_type r) (r_fields r)) $$
    rrecord

ppConfig ty fs =
    let docs = (ppConfigMap M.! ty) (makeFieldMap fs)
        prefix = (lowerNameMap M.! ty) ++ "_"
    in [assign (prefix ++ fn) val | (fn, val) <- docs]

ppState ty fs =
    let docs = (ppStateMap M.! ty) (makeFieldMap fs)
        prefix = (lowerNameMap M.! ty) ++ "_"
    in [assign (prefix ++ fn) val | (fn, val) <- docs]

makeFieldMap fs = M.fromList [(fn, val) | (fn, [Literal val]) <- fs]


-- Main entry point

toCoq db = print $ vcat $
    [ header
    , blank, recordNames db
    , blank, recordConfigs db
    , blank, recordStates db
    ]

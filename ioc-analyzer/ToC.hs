{-# LANGUAGE StandaloneDeriving #-}
module ToC
where

import Control.Applicative ((<$>))
import Control.Monad
import qualified Data.Map as M
import Data.Maybe

import Text.PrettyPrint.HughesPJ

import ExpParser
import Iocsh
import Record
import ToExtraction
import Multi
import qualified HL

import qualified Query as Q

import Debug.Trace


dot = char '.'


ppDatabase :: Q.Database_config -> Q.Database_state -> Doc
ppDatabase dbc dbs =
    text "// AUTOGENERATED FILE - DO NOT EDIT" $+$
    text "#include \"epics.h\"" $+$
    text "" $+$
    vcat (punctuate (text "") (
        zipWith (\rn _ -> text "void" <+> ppProcessFuncName rn <> lparen <> rparen <> semi)
                [0..] dbc ++
        zipWith3 (\rn rc rs -> text "" $+$ ppRecord rn rc rs)
                [0..] dbc dbs
    ))


ppRecord :: Q.Record_name -> Q.Record_config -> Q.Record_state -> Doc
ppRecord rn (Q.RcCalc cfg) (Q.RsCalc st) =
    let Q.CalcConfig calc inpa_to_inpl flnk = cfg
        Q.CalcState a2l val = st
        fields = [(Q.F_A_to_L i, ppFloat $ multiGet a2l (fromInteger i)) | i <- [0 .. 11]] ++
            [(Q.F_VAL, ppFloat val)]
    in
        ppRecordInit rn "calc" fields $+$
        ppProcessFunc rn (
            ppReadOptInLinkInto (rn, Q.F_A_to_L 0) (multiGet inpa_to_inpl 0) $+$
            ppReadOptInLinkInto (rn, Q.F_A_to_L 1) (multiGet inpa_to_inpl 1) $+$
            hsep [ppFieldAccess rn Q.F_VAL, equals, int 42 {- TODO -}] <> semi $+$
            ppProcessOptFwdLink flnk
        )

ppRecordInit rn typ fields =
    hsep [text "struct", text "record_" <> text typ, text "r" <> integer rn, equals, lbrace] $+$
    nest 4 (vcat $ map ppFieldInit fields) $+$
    rbrace <> semi

ppFieldInit (fn, doc) = hsep [dot <> ppFieldName fn, equals, doc] <> comma

ppFieldName (Q.F_A_to_L i) = text [toEnum ((fromEnum 'A') + fromInteger i)]
ppFieldName Q.F_VAL = text "VAL"
ppFieldName Q.F_OVAL = text "OVAL"

ppNat n = integer $ n
ppFloat n = double $ unconvFloat n

ppProcessFunc rn body =
    text "void" <+> ppProcessFuncName rn <> lparen <> rparen <+> lbrace $+$
    nest 4 body $+$
    rbrace

ppProcessFuncName rn = text "process_" <> integer rn

ppReadOptInLinkInto :: (Q.Record_name, Q.Field_name) -> Q.In_link -> Doc
ppReadOptInLinkInto (drn, dfn) Q.InLinkNull = empty
ppReadOptInLinkInto (drn, dfn) (Q.InLinkConstant x) = ppFloat x
ppReadOptInLinkInto (drn, dfn) (Q.InLinkField (Q.FieldLink srn sfn _)) =
    hsep [ppFieldAccess drn dfn, equals, ppFieldAccess srn sfn] <> semi

ppProcessOptFwdLink :: Q.Fwd_link -> Doc
ppProcessOptFwdLink Q.FwdLinkNull = empty
ppProcessOptFwdLink (Q.FwdLinkRecord rn) =
    ppProcessFuncName rn <> lparen <> rparen <> semi

ppFieldAccess rn fn = text "r" <> integer rn <> dot <> ppFieldName fn




toC hsDb = do
    let (hldb, errs) = HL.parseDatabase hsDb
        hldb' = if null errs then hldb else error $ show errs
        (dbc, dbs) = (conv hldb', conv hldb')
    print $ ppDatabase dbc dbs


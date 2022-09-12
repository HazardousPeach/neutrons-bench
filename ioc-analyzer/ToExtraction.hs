{-# LANGUAGE
        MultiParamTypeClasses,
        FlexibleInstances,
        FlexibleContexts,
        DataKinds,
        StandaloneDeriving
    #-}
module ToExtraction
where

import Control.Applicative ((<$>), (<*>))
import Control.Lens hiding ((^.), use)
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Data.Bits
import Data.Fixed
import Data.List (intercalate)
import qualified Data.Map as M
import Data.Maybe
import Data.Word
import Unsafe.Coerce
import qualified GHC.Prim (Any)

import ExpParser
import Iocsh
import Parser
import Record
import Multi

import HL ((^.))
import qualified HL
import qualified CalcExp as CE
import qualified Query as Q

import Debug.Trace


instance Show Q.Value where
    show (Q.VDouble x) = show x
    show (Q.VString x) = show x
    show (Q.VEnum _ x) = show x
    show (Q.VLong x) = show x
    show (Q.VArray elem size _) = "[array: " ++ show elem ++ " * " ++ show size ++ "]"
deriving instance Show Q.Elem_type
deriving instance Show Q.Field_type
deriving instance Show Q.Field_type_matcher
deriving instance Show Q.Record_program
deriving instance Show Q.Record_type
deriving instance Show Q.Field_link
deriving instance Show Q.In_link
deriving instance Show Q.Out_link
deriving instance Show Q.Fwd_link
deriving instance Show Q.Process_passive_flag
deriving instance Show Q.Error

deriving instance Show Q.Unary_op
deriving instance Show Q.Binary_op
deriving instance Show Q.Varary_op
deriving instance Show a => Show (Q.Expr a)
deriving instance Show Q.Output_exec
deriving instance Show Q.Umicro
deriving instance Show Q.Type_error_context
deriving instance Show Q.Type_error

deriving instance Show Q.Wf_error_context
deriving instance Show Q.Wf_error

deriving instance Show Q.Error0

deriving instance Show Q.Calc_abs
deriving instance Show Q.Calc_out_abs
deriving instance Show Q.Str_calc_out_abs
deriving instance Show Q.Array_calc_out_abs
deriving instance Show Q.Fanout_abs
--deriving instance Show Q.Analog_in_abs
deriving instance Show Q.Analog_out_abs
--deriving instance Show Q.Binary_in_abs
--deriving instance Show Q.Binary_out_abs
--deriving instance Show Q.Mbbo_abs
deriving instance Show Q.String_in_abs
deriving instance Show Q.String_out_abs
--deriving instance Show Q.Long_in_abs
--deriving instance Show Q.Long_out_abs
--deriving instance Show Q.Dfanout_abs
--deriving instance Show Q.Seq_abs
deriving instance Show Q.Waveform_abs
deriving instance Show Q.Subarray_abs
deriving instance Show Q.Asyn_abs

deriving instance Show Q.Record_abs


deriving instance Eq Q.Elem_type

deriving instance Eq Q.Calc_abs
deriving instance Eq Q.Calc_out_abs
deriving instance Eq Q.Str_calc_out_abs
deriving instance Eq Q.Array_calc_out_abs
deriving instance Eq Q.Fanout_abs
--deriving instance Eq Q.Analog_in_abs
deriving instance Eq Q.Analog_out_abs
--deriving instance Eq Q.Binary_in_abs
--deriving instance Eq Q.Binary_out_abs
--deriving instance Eq Q.Mbbo_abs
deriving instance Eq Q.String_in_abs
deriving instance Eq Q.String_out_abs
--deriving instance Eq Q.Long_in_abs
--deriving instance Eq Q.Long_out_abs
--deriving instance Eq Q.Dfanout_abs
--deriving instance Eq Q.Seq_abs
deriving instance Eq Q.Waveform_abs
deriving instance Eq Q.Subarray_abs
deriving instance Eq Q.Asyn_abs

deriving instance Eq Q.Record_abs


instance Show Q.E_double where
    show f = show $ (conv f :: Double)

instance Show Q.E_string where
    show s = show $ (conv s :: String)

instance Show Q.Field_name where
    show Q.F_VAL = "F_VAL"
    show Q.F_PVAL = "F_PVAL"
    show Q.F_OVAL = "F_OVAL"
    show Q.F_SVAL = "F_SVAL"
    show Q.F_OSV = "F_OSV"
    show Q.F_AVAL = "F_AVAL"
    show Q.F_OAV = "F_OAV"
    show (Q.F_A_to_L idx) = "F_" ++ [HL.indexToLetter (fromIntegral idx)]
    show (Q.F_AA_to_LL idx) = let c = HL.indexToLetter (fromIntegral idx) in "F_" ++ [c,c]
    show (Q.F_DO1_to_DOA idx) = "F_DO" ++ [HL.indexToChar (fromIntegral idx)]
    show Q.F_PACT = "F_PACT"
    show Q.F_PROC = "F_PROC"
    show (Q.F_tmp idx) = "F_tmp_" ++ show idx

allFields =
    -- debug only
    -- f_PVAL :
    -- f_PACT :
    -- f_tmp 0 :
    [Q.F_VAL, Q.F_OVAL] ++
    [Q.F_SVAL, Q.F_OSV] ++
    [Q.F_A_to_L i | i <- [0 .. 11]] ++
    [Q.F_AA_to_LL i | i <- [0 .. 11]] ++
    [Q.F_DO1_to_DOA i | i <- [0 .. 9]]


instance Show Q.Micro where
    show (Q.MSetConst fn val) = "MSetConst " ++ show fn ++ " " ++ show val
    show (Q.MCopy fn ft fn' ft') = "MCopy " ++ show fn ++ " " ++ show ft ++
        " " ++ show fn' ++ " " ++ show ft'
    show (Q.MReadLink il ft fn' ft') = "MReadLink " ++ show il ++ " " ++ show ft ++
        " " ++ show fn' ++ " " ++ show ft'
    show _ = "(not yet implemented)"



data Ctx = Ctx
    { ctx_name_map :: M.Map String Integer
    }


class Convert a b where
    conv :: a -> b

type M a = Reader Ctx a

class MConvert a b where
    mconv :: a -> M b


instance Convert Double Q.E_double where
    conv f = Q.b64_of_bits $ fromIntegral $ (unsafeCoerce :: Double -> Word64) f

instance Convert Q.E_double Double where
    conv f = (unsafeCoerce :: Word64 -> Double) $ fromIntegral $ Q.bits_of_b64 f

instance Convert Int Bool where
    conv 0 = False
    conv _ = True

convEnum :: Integer -> Integer -> Q.E_enum
convEnum max x | x >= max = error $ "convEnum: " ++ show x ++ " >= " ++ show max
convEnum max x = x

convEnumValue :: Integer -> Integer -> Q.Value
convEnumValue max x | x >= max = error $ "convEnumValue: " ++ show x ++ " >= " ++ show max
convEnumValue max x = Q.VEnum max x

convLong :: Integer -> Q.E_long
convLong x | x >= Q.lONG_MAX = error $ "convLong: " ++ show x ++ " >= LONG_MAX"
convLong x | x < -Q.lONG_MAX = error $ "convLong: " ++ show x ++ " < -LONG_MAX"
convLong x = x

convLongValue :: Integer -> Q.Value
convLongValue x | x >= Q.lONG_MAX = error $ "convLongValue: " ++ show x ++ " >= LONG_MAX"
convLongValue x | x < -Q.lONG_MAX = error $ "convLongValue: " ++ show x ++ " < -LONG_MAX"
convLongValue x = Q.VLong x

instance Convert Q.Ascii0 Char where
    conv (Q.Ascii x0 x1 x2 x3 x4 x5 x6 x7) = toEnum $
        (if x0 then 1 else 0) `shiftL` 0 .|.
        (if x1 then 1 else 0) `shiftL` 1 .|.
        (if x2 then 1 else 0) `shiftL` 2 .|.
        (if x3 then 1 else 0) `shiftL` 3 .|.
        (if x4 then 1 else 0) `shiftL` 4 .|.
        (if x5 then 1 else 0) `shiftL` 5 .|.
        (if x6 then 1 else 0) `shiftL` 6 .|.
        (if x7 then 1 else 0) `shiftL` 7

instance Convert Char Q.Ascii0 where
    conv c | i <- fromEnum c, i < 256 = Q.Ascii
        (testBit i 0)
        (testBit i 1)
        (testBit i 2)
        (testBit i 3)
        (testBit i 4)
        (testBit i 5)
        (testBit i 6)
        (testBit i 7)

instance Convert Q.String String where
    conv Q.EmptyString = ""
    conv (Q.String0 a s) = conv a : conv s

instance Convert String Q.String where
    conv "" = Q.EmptyString
    conv (a : s) = Q.String0 (conv a) (conv s)

instance Convert HL.MenuOOpt Q.Output_exec where
    conv HL.OOpt_EveryTime = Q.EveryTime
    conv HL.OOpt_OnChange = Q.OnChange
    conv HL.OOpt_WhenZero = Q.WhenZero
    conv HL.OOpt_WhenNonzero = Q.WhenNonzero
    conv HL.OOpt_TransitionToZero = Q.TransitionToZero
    conv HL.OOpt_TransitionToNonzero = Q.TransitionToNonzero

instance Convert HL.MenuDOpt Q.Output_data where
    conv HL.DOpt_UseCALC = Q.UseCalc
    conv HL.DOpt_UseOCAL = Q.UseOcal


instance Convert CE.Exp (Q.Expr Q.E_double) where
    conv (CE.Var idx) = Q.EVar $ fromIntegral idx
    conv (CE.XVar idx) = Q.EXVar $ fromIntegral idx
    conv (CE.Lit val) = Q.ELit (conv val)
    conv (CE.Unary op a) = Q.EUnary (conv op) (conv a)
    conv (CE.Binary op a b) = Q.EBinary (conv op) (conv a) (conv b)
    conv (CE.Ternary CE.Cond a b c) = Q.ECond (conv a) (conv b) (conv c)
    conv (CE.Ternary _ a b c) = Q.ECond (conv a) (conv b) (conv c) -- TODO
    --conv (CE.Ternary op a b c) = error $ "not yet implemented: " ++ show op
    --conv (CE.Varary op args) = Q.EVarary (conv op) (map conv args)
    conv (CE.Varary op args) = Q.EVarary (conv op) (map conv args)
    conv (CE.Assign idx x) = Q.EAssign (fromIntegral idx) (conv x)
    conv (CE.XAssign idx x) = Q.EXAssign (fromIntegral idx) (conv x)
    conv (CE.Seq a b) = Q.ESeq (conv a) (conv b)

instance Convert CE.Exp (Q.Expr (Either Q.E_double Q.E_string)) where
    conv (CE.Var idx) = Q.EVar $ fromIntegral idx
    conv (CE.XVar idx) = Q.EXVar $ fromIntegral idx
    conv (CE.Lit val) = Q.ELit (Left (conv val))
    conv (CE.LitStr val) = Q.ELit (Right (conv val))
    conv (CE.Unary op a) = Q.EUnary (conv op) (conv a)
    conv (CE.Binary op a b) = Q.EBinary (conv op) (conv a) (conv b)
    conv (CE.Ternary CE.Cond a b c) = Q.ECond (conv a) (conv b) (conv c)
    conv (CE.Ternary _ a b c) = Q.ECond (conv a) (conv b) (conv c) -- TODO
    --conv (CE.Ternary op a b c) = error $ "not yet implemented: " ++ show op
    --conv (CE.Varary op args) = Q.EVarary (conv op) (map conv args)
    conv (CE.Varary op args) = Q.EVarary (conv op) (map conv args)
    conv (CE.Assign idx x) = Q.EAssign (fromIntegral idx) (conv x)
    conv (CE.XAssign idx x) = Q.EXAssign (fromIntegral idx) (conv x)
    conv (CE.Seq a b) = Q.ESeq (conv a) (conv b)

-- Need a funny hack here for exprs over arrays.  We can't declare an instance
-- for any type involving GHC.Prim.Any, which Q.E_array is an alias for.
-- Instead we declare the instance with a dummy type in its place, and coerce
-- after the conversion.
data E_array_dummy = E_array_dummy

coerceArrayExpr ::
    Q.Expr (Either Q.E_double E_array_dummy) ->
    Q.Expr (Either Q.E_double Q.E_array)
coerceArrayExpr = unsafeCoerce

instance Convert CE.Exp (Q.Expr (Either Q.E_double E_array_dummy)) where
    conv (CE.Var idx) = Q.EVar $ fromIntegral idx
    conv (CE.XVar idx) = Q.EXVar $ fromIntegral idx
    conv (CE.Lit val) = Q.ELit (Left (conv val))
    conv (CE.Unary op a) = Q.EUnary (conv op) (conv a)
    conv (CE.Binary op a b) = Q.EBinary (conv op) (conv a) (conv b)
    conv (CE.Ternary CE.Cond a b c) = Q.ECond (conv a) (conv b) (conv c)
    conv (CE.Ternary op a b c) = error $ "not yet implemented: " ++ show op
    --conv (CE.Varary op args) = Q.EVarary (conv op) (map conv args)
    conv (CE.Varary op args) = Q.EVarary (conv op) (map conv args)
    conv (CE.Assign idx x) = Q.EAssign (fromIntegral idx) (conv x)
    conv (CE.XAssign idx x) = Q.EXAssign (fromIntegral idx) (conv x)
    conv (CE.Seq a b) = Q.ESeq (conv a) (conv b)

instance Convert CE.UnOp Q.Unary_op where
    conv CE.NotAlg = Q.NotAlg
    conv CE.NotLog = Q.NotLog
    conv op = Q.NotAlg -- TODO
    --conv op = error $ "unsupported: unary operator " ++ show op

instance Convert CE.BinOp Q.Binary_op where
    conv CE.Add = Q.Add
    conv CE.Sub = Q.Sub
    conv CE.Mul = Q.Mul
    conv CE.Div = Q.Div
    conv CE.Eq = Q.Eq0      -- -0 suffix due to overlap with comparison.Eq
    conv CE.Ne = Q.Ne
    conv CE.Gt = Q.Gt0
    conv CE.Ge = Q.Ge
    conv CE.Lt = Q.Lt0
    conv CE.Le = Q.Le
    conv CE.AndLog = Q.AndLog
    conv CE.OrLog = Q.OrLog
    conv op = Q.Add -- TODO
    --conv op = error $ "unsupported: binary operator " ++ show op

instance Convert CE.VarOp Q.Varary_op where
    conv CE.Min = Q.Min
    conv CE.Max = Q.Max
    conv op = error $ "unsupported: varary operator " ++ show op


instance MConvert FieldLink Q.In_link where
    mconv NoLink =
        return Q.InLinkNull
    mconv (HardwareAddr _) =
        return Q.InLinkNull -- TODO
    mconv (Constant x) =
        return $ Q.InLinkConstant $ conv x
    mconv (fl@FieldLink {}) = do
        mRn <- asks $ M.lookup (fl_record fl) . ctx_name_map
        let rn = case mRn of 
                Just x -> x
                Nothing -> error $ "bad record name in FieldLink: " ++ fl_record fl
        let fn = conv $ fl_field fl
        let pp = conv $ fl_pp fl
        return $ Q.InLinkField $ Q.FieldLink rn fn pp

instance MConvert FieldLink Q.Out_link where
    mconv NoLink =
        return Q.OutLinkNull
    mconv (HardwareAddr _) =
        return Q.OutLinkNull -- TODO
    mconv (Constant _) =
        error $ "constant addresses are not supported for Out_link"
    mconv (fl@FieldLink {}) = do
        mRn <- asks $ M.lookup (fl_record fl) . ctx_name_map
        let rn = case mRn of 
                Just x -> x
                Nothing -> error $ "bad record name in FieldLink: " ++ fl_record fl
        let fn = conv $ fl_field fl
        let pp = conv $ fl_pp fl
        return $ Q.OutLinkField $ Q.FieldLink rn fn pp

instance MConvert RecordLink Q.Fwd_link where
    mconv NoRLink =
        return Q.FwdLinkNull
    mconv (rl@RecordLink {}) = do
        mRn <- asks $ M.lookup (rl_record rl) . ctx_name_map
        let rn = case mRn of 
                Just x -> x
                Nothing -> error $ "bad record name in RecordLink: " ++ rl_record rl
        return $ Q.FwdLinkRecord $ rn

instance Convert String Q.Field_name where
    conv "VAL" = Q.F_VAL
    conv "OVAL" = Q.F_OVAL
    conv [c] | Just idx <- HL.letterToIndex 12 c =
        Q.F_A_to_L $ fromIntegral idx
    conv [c, c'] | c == c', Just idx <- HL.letterToIndex 12 c =
        Q.F_AA_to_LL $ fromIntegral idx
    conv ['D', 'O', c]  | Just idx <- HL.charToIndex 10 c =
        Q.F_DO1_to_DOA $ fromIntegral idx
    conv "PROC" = Q.F_PROC
    conv _ = Q.F_tmp 0 -- TODO
    --conv name = error $ "unsupported: field name " ++ show name

instance Convert PpFlag Q.Process_passive_flag where
    conv NoProcessPassive = Q.NPP
    conv ProcessPassive = Q.PP

instance Convert HL.MenuFtype Q.Elem_type where
    conv HL.Ftype_String = Q.TeString
    conv HL.Ftype_Char = Q.TeLong -- TODO
    conv HL.Ftype_UChar = Q.TeLong -- TODO
    conv HL.Ftype_Short = Q.TeLong -- TODO
    conv HL.Ftype_UShort = Q.TeLong -- TODO
    conv HL.Ftype_Long = Q.TeLong
    conv HL.Ftype_ULong = Q.TeLong -- TODO
    conv HL.Ftype_Double = Q.TeDouble
    conv HL.Ftype_Enum = Q.TeLong -- TODO


--
-- Config conversion
--

instance MConvert HL.HlRecord Q.Record_config where
    mconv hlr = case hlr ^. HL.detail of
        d@HL.Calc{} -> Q.RcCalc <$> convCalcConfig hlr d
        d@HL.CalcOut{} -> Q.RcCalcOut <$> convCalcOutConfig hlr d
        d@HL.StrCalcOut{} -> Q.RcStrCalcOut <$> convStrCalcOutConfig hlr d
        d@HL.ArrayCalcOut{} -> convArrayCalcOutConfig hlr d
        d@HL.Fanout{} -> Q.RcFanout <$> convFanoutConfig hlr d
        d@HL.DFanout{} -> Q.RcDFanout <$> convDFanoutConfig hlr d
        d@HL.Seq{} -> Q.RcSeq <$> convSeqConfig hlr d
        d@HL.AnalogIn{} -> Q.RcAnalogIn <$> convAnalogInConfig hlr d
        d@HL.AnalogOut{} -> Q.RcAnalogOut <$> convAnalogOutConfig hlr d
        d@HL.BinaryIn{} -> Q.RcBinaryIn <$> convBinaryInConfig hlr d
        d@HL.BinaryOut{} -> Q.RcBinaryOut <$> convBinaryOutConfig hlr d
        d@HL.MBBO{} -> Q.RcMBBO <$> convMBBOConfig hlr d
        d@HL.StringIn{} -> Q.RcStringIn <$> convStringInConfig hlr d
        d@HL.StringOut{} -> Q.RcStringOut <$> convStringOutConfig hlr d
        d@HL.LongIn{} -> Q.RcLongIn <$> convLongInConfig hlr d
        d@HL.LongOut{} -> Q.RcLongOut <$> convLongOutConfig hlr d
        d@HL.Waveform{} -> convWaveformConfig hlr d
        d@HL.SubArray{} -> convSubArrayConfig hlr d
        d@HL.Asyn{} -> Q.RcAsyn <$> convAsynConfig hlr d
        d -> error $ "unsupported record type (config): " ++ show (HL.hlRecordType d)

convCalcConfig hlr d = Q.CalcConfig
    <$> pure (conv $ d ^. HL.calc_CALC)
    <*> multiMapM (mconv :: FieldLink -> M Q.In_link) (d ^. HL.calc_INPA_to_INPL)
    <*> mconv (hlr ^. HL.hlr_FLNK)

convCalcOutConfig hlr d = Q.CalcOutConfig
    <$> pure (conv $ d ^. HL.calcout_CALC)
    <*> pure (conv $ d ^. HL.calcout_OCAL)
    <*> multiMapM (mconv :: FieldLink -> M Q.In_link) (d ^. HL.calcout_INPA_to_INPL)
    <*> mconv (d ^. HL.calcout_OUT)
    <*> mconv (hlr ^. HL.hlr_FLNK)
    <*> pure (conv $ d ^. HL.calcout_OOPT)
    <*> pure (conv $ d ^. HL.calcout_DOPT)

convStrCalcOutConfig hlr d = Q.StrCalcOutConfig
    <$> pure (conv $ d ^. HL.scalcout_CALC)
    <*> pure (conv $ d ^. HL.scalcout_OCAL)
    <*> multiMapM (mconv :: FieldLink -> M Q.In_link) (d ^. HL.scalcout_INPA_to_INPL)
    <*> multiMapM (mconv :: FieldLink -> M Q.In_link) (d ^. HL.scalcout_INAA_to_INLL)
    <*> mconv (d ^. HL.scalcout_OUT)
    <*> mconv (hlr ^. HL.hlr_FLNK)
    <*> pure (conv $ d ^. HL.scalcout_OOPT)
    <*> pure (conv $ d ^. HL.scalcout_DOPT)

convArrayCalcOutConfig hlr d =
    let n = fromIntegral (d ^. HL.acalcout_NELM)
    in Q.RcArrayCalcOut n <$> (Q.ArrayCalcOutConfig
        <$> pure (coerceArrayExpr $ conv $ d ^. HL.acalcout_CALC)
        <*> pure (coerceArrayExpr $ conv $ d ^. HL.acalcout_OCAL)
        <*> multiMapM (mconv :: FieldLink -> M Q.In_link) (d ^. HL.acalcout_INPA_to_INPL)
        <*> multiMapM (mconv :: FieldLink -> M Q.In_link) (d ^. HL.acalcout_INAA_to_INLL)
        <*> mconv (d ^. HL.acalcout_OUT)
        <*> mconv (hlr ^. HL.hlr_FLNK)
        <*> pure (conv $ d ^. HL.acalcout_OOPT)
        <*> pure (conv $ d ^. HL.acalcout_DOPT))

convFanoutConfig hlr d = id
    <$> multiMapM (mconv :: RecordLink -> M Q.Fwd_link) (d ^. HL.fanout_LNK1_to_LNK6)

convDFanoutConfig hlr d = Q.DFanoutConfig
    <$> mconv (d ^. HL.dfanout_DOL)
    <*> multiMapM (mconv :: FieldLink -> M Q.Out_link) (d ^. HL.dfanout_OUTA_to_OUTH)
    <*> mconv (hlr ^. HL.hlr_FLNK)

convSeqConfig hlr d = Q.SeqConfig
    <$> multiMapM (mconv :: FieldLink -> M Q.In_link) (d ^. HL.seq_DOL1_to_DOLA)
    <*> multiMapM (mconv :: FieldLink -> M Q.Out_link) (d ^. HL.seq_LNK1_to_LNKA)

convAnalogInConfig hlr d = id
    <$> mconv (hlr ^. HL.hlr_FLNK)

convAnalogOutConfig hlr d = Q.AnalogOutConfig
    <$> mconv (d ^. HL.ao_DOL)
    <*> mconv (hlr ^. HL.hlr_FLNK)

convBinaryInConfig hlr d = id
    <$> mconv (hlr ^. HL.hlr_FLNK)

convBinaryOutConfig hlr d = Q.BinaryOutConfig
    <$> mconv (d ^. HL.bo_DOL)
    <*> mconv (hlr ^. HL.hlr_FLNK)

convMBBOConfig hlr d = Q.MBBOConfig
    <$> mconv (d ^. HL.mbbo_DOL)
    <*> mconv (hlr ^. HL.hlr_FLNK)

convStringInConfig hlr d = id
    <$> mconv (hlr ^. HL.hlr_FLNK)

convStringOutConfig hlr d = Q.StringOutConfig
    <$> mconv (d ^. HL.stringout_DOL)
    <*> mconv (hlr ^. HL.hlr_FLNK)

convLongInConfig hlr d = id
    <$> mconv (hlr ^. HL.hlr_FLNK)

convLongOutConfig hlr d = Q.LongOutConfig
    <$> mconv (d ^. HL.longout_DOL)
    <*> mconv (hlr ^. HL.hlr_FLNK)

convWaveformConfig hlr d =
    let ty = conv (d ^. HL.waveform_FTVL)
        n = fromIntegral (d ^. HL.waveform_NELM)
    in Q.RcWaveform ty n <$> (Q.WaveformConfig
        <$> mconv (d ^. HL.waveform_INP)
        <*> mconv (hlr ^. HL.hlr_FLNK))

convSubArrayConfig hlr d =
    let ty = conv (d ^. HL.subarray_FTVL)
        n = fromIntegral (d ^. HL.subarray_NELM)
        m = fromIntegral (d ^. HL.subarray_MALM)
    in Q.RcSubarray ty n m <$> (Q.SubarrayConfig
        <$> mconv (d ^. HL.subarray_INP)
        <*> pure (fromIntegral $ d ^. HL.subarray_INDX)
        <*> mconv (hlr ^. HL.hlr_FLNK))

convAsynConfig hlr d = return Q.AsynConfig

--
-- State conversion
--

instance Convert HL.HlRecord Q.Record_state where
    conv hlr = case hlr ^. HL.detail of
        d@HL.Calc{} -> Q.RsCalc (convCalcState hlr d)
        d@HL.CalcOut{} -> Q.RsCalcOut (convCalcOutState hlr d)
        d@HL.StrCalcOut{} -> Q.RsStrCalcOut (convStrCalcOutState hlr d)
        d@HL.ArrayCalcOut{} -> convArrayCalcOutState hlr d
        d@HL.Fanout{} -> Q.RsFanout (convFanoutState hlr d)
        d@HL.DFanout{} -> Q.RsDFanout (convDFanoutState hlr d)
        d@HL.Seq{} -> Q.RsSeq (convSeqState hlr d)
        d@HL.AnalogIn{} -> Q.RsAnalogIn (convAnalogInState hlr d)
        d@HL.AnalogOut{} -> Q.RsAnalogOut (convAnalogOutState hlr d)
        d@HL.BinaryIn{} -> Q.RsBinaryIn (convBinaryInState hlr d)
        d@HL.BinaryOut{} -> Q.RsBinaryOut (convBinaryOutState hlr d)
        d@HL.MBBO{} -> Q.RsMBBO (convMBBOState hlr d)
        d@HL.StringIn{} -> Q.RsStringIn (convStringInState hlr d)
        d@HL.StringOut{} -> Q.RsStringOut (convStringOutState hlr d)
        d@HL.LongIn{} -> Q.RsLongIn (convLongInState hlr d)
        d@HL.LongOut{} -> Q.RsLongOut (convLongOutState hlr d)
        d@HL.Waveform{} -> convWaveformState hlr d
        d@HL.SubArray{} -> convSubArrayState hlr d
        d@HL.Asyn{} -> Q.RsAsyn (convAsynState hlr d)
        d -> error $ "unsupported record type (state): " ++ show (HL.hlRecordType d)

convCalcState hlr d = Q.CalcState
    (multiMap (conv :: Double -> Q.E_double) (d ^. HL.calc_A_to_L))
    (conv $ d ^. HL.calc_VAL)

convCalcOutState hlr d = Q.CalcOutState
    (multiMap (conv :: Double -> Q.E_double) (d ^. HL.calcout_A_to_L))
    (conv $ d ^. HL.calcout_VAL)
    (conv $ d ^. HL.calcout_VAL) -- PVAL
    (conv $ d ^. HL.calcout_OVAL)
    (conv (0 :: Double)) -- tmp0

convStrCalcOutState hlr d = Q.StrCalcOutState
    (multiMap (conv :: Double -> Q.E_double) (d ^. HL.scalcout_A_to_L))
    (multiMap (conv :: String -> Q.E_string) (d ^. HL.scalcout_AA_to_LL))
    (conv $ d ^. HL.scalcout_VAL)
    (conv $ d ^. HL.scalcout_SVAL)
    (conv $ d ^. HL.scalcout_VAL) -- PVAL
    (conv $ d ^. HL.scalcout_OVAL)
    (conv $ d ^. HL.scalcout_OSV)
    (conv (0 :: Double)) -- tmp0

convArrayCalcOutState hlr d =
    let n = fromIntegral (d ^. HL.subarray_NELM)
        arr = Q.default_array Q.TeDouble n
    in Q.RsArrayCalcOut n (Q.ArrayCalcOutState
        (multiMap (conv :: Double -> Q.E_double) (d ^. HL.acalcout_A_to_L))
        (toMulti $ replicate 12 arr)
        (conv $ d ^. HL.acalcout_VAL)
        (arr)
        (conv $ d ^. HL.acalcout_VAL) -- PVAL
        (conv $ d ^. HL.acalcout_OVAL)
        (arr)
        (conv (0 :: Double))) -- tmp0

convFanoutState hlr d = Q.FanoutState

convDFanoutState hlr d = id
    (conv $ d ^. HL.dfanout_VAL)

convSeqState hlr d = Q.SeqState
    (multiMap (conv :: Double -> Q.E_double) (d ^. HL.seq_DO1_to_DOA))
    (0)

convAnalogInState hlr d = id
    (conv $ d ^. HL.ai_VAL)

convAnalogOutState hlr d = Q.AnalogOutState
    (conv $ d ^. HL.ao_VAL)
    (conv $ d ^. HL.ao_VAL) -- PVAL

convBinaryInState hlr d = id
    (convEnum 2 $ fromIntegral $ d ^. HL.bi_VAL)

convBinaryOutState hlr d = id
    (convEnum 2 $ fromIntegral $ d ^. HL.bo_VAL)

convMBBOState hlr d = id
    (convEnum 16 $ fromIntegral $ d ^. HL.mbbo_VAL)

convStringInState hlr d = id
    (conv $ d ^. HL.stringin_VAL)

convStringOutState hlr d = id
    (conv $ d ^. HL.stringout_VAL)

convLongInState hlr d = id
    (convLong $ fromIntegral $ d ^. HL.longin_VAL)

convLongOutState hlr d = id
    (convLong $ fromIntegral $ d ^. HL.longout_VAL)

convWaveformState hlr d =
    let ty = conv (d ^. HL.waveform_FTVL)
        n = fromIntegral (d ^. HL.waveform_NELM)
        arr = Q.default_array ty n
    in Q.RsWaveform ty n (id
        (arr))  -- VAL

convSubArrayState hlr d =
    let ty = conv (d ^. HL.subarray_FTVL)
        n = fromIntegral (d ^. HL.subarray_NELM)
        m = fromIntegral (d ^. HL.subarray_MALM)
        arrN = Q.default_array ty n
        arrM = Q.default_array ty m
    in Q.RsSubarray ty n m (Q.SubarrayState
        (arrN)  -- VAL
        (arrM)) -- tmp0

convAsynState hlr d = Q.AsynState


instance Convert HL.HlDatabase [Q.Record_config] where
    conv db =
        let (names, recs) = unzip $ M.toList db
            nameMap = hldbNameToId db
            ctx = Ctx nameMap
        in runReader (mapM mconv recs) ctx

instance Convert HL.HlDatabase [Q.Record_state] where
    conv db =
        let (names, recs) = unzip $ M.toList db
        in map conv recs


unconvFloat :: Q.E_double -> Double
unconvFloat = conv


initState :: M.Map Int String -> Q.Database_config -> Q.Database_state -> Q.Valid_state
initState nameMap dbc dbs =
    case Q.init_state dbc dbs of
        Left vs -> vs
        Right err -> error $ showError nameMap "init error:" err

runStateLoop :: Q.Valid_state -> Q.Time -> (Q.Valid_state, [Q.Output_event])
runStateLoop vs now = go vs []
  where
    go vs oes =
        case Q.run_state vs now of
            Left (Q.Existp vs' oes') -> go vs' (oes ++ oes')
            Right _ -> (vs, oes)    -- No more events with time <= now

enqueueEvent :: Q.Valid_state -> Q.Time -> Q.Input_event -> Q.Valid_state
enqueueEvent vs when ie =
    case Q.enqueue_event vs when ie of
        Just vs' -> vs'
        Nothing -> error "enqueue_event failed"

readValue :: String -> Q.Value
readValue s | [(x,"")] <- reads s = convEnumValue 2 x
readValue s | [(x,"")] <- reads s = Q.VDouble $ (conv :: Double -> Q.E_double) $ x
readValue s = Q.VString $ (conv :: String -> Q.E_string) $ s

readValueAsType :: Q.Field_type -> String -> Q.Value
readValueAsType Q.TDouble s
    | [(x,"")] <- reads s = Q.VDouble $ (conv :: Double -> Q.E_double) $ x
    | otherwise = error $ "expected double, but got " ++ show s
readValueAsType Q.TString s = Q.VString $ (conv :: String -> Q.E_string) $ s
readValueAsType (Q.TEnum max) s
    | [(x,"")] <- reads s = convEnumValue max x
    | otherwise = error $ "expected enum, but got " ++ show s
readValueAsType Q.TLong s
    | [(x,"")] <- reads s = convLongValue x
    | otherwise = error $ "expected long, but got " ++ show s

runExtraction :: [Command] -> HL.HlDatabase -> IO ()
runExtraction cmds hldb =
    seq vs0 $
        void $ foldM go vs0 cmds
  where
    dbc :: Q.Database_config
    dbc = conv hldb
    dbs :: Q.Database_state
    dbs = conv hldb

    vs0 = initState (hldbNameMap hldb) dbc dbs

    (recordNames, recs) = unzip $ M.toList hldb
    nameMap = hldbNameToId hldb
    recordId name =
        case M.lookup name nameMap of
            Just x -> x
            Nothing -> error $ "link to nonexistent record: " ++ name

    go :: Q.Valid_state -> Command -> IO Q.Valid_state
    go vs (FuncCmd "dbgf" [rfn]) = getField vs rfn
    go vs (FuncCmd "dbpf" [rfn, val]) = putField vs rfn val
    go vs (FuncCmd "dbtr" [rn]) = process vs rn
    go vs _ = return vs

    getField :: Q.Valid_state -> String -> IO Q.Valid_state
    getField vs rfn = do
        let (FieldLink rn fn NoProcessPassive NonMaximizeSeverity) = parseFieldLink rfn
        let rn' = recordId rn
        let fn' = conv fn
        print $ fromMaybe (error $ "dbgf failed" ++ rfn) $ Q.field_read vs rn' fn'
        return vs

    putField :: Q.Valid_state -> String -> String -> IO Q.Valid_state
    putField vs rfn val = do
        let (FieldLink rn fn NoProcessPassive NonMaximizeSeverity) = parseFieldLink rfn
        let rn' = recordId rn
        let fn' = conv fn
        let rt = Q.record_state_type (Q.sys_dbs (Q.vs_sys vs) !! fromIntegral rn')
        let ft = Q.record_field_type rt fn'
        let val' = readValueAsType ft val
        return $ fromMaybe (error $ "dbpf failed: " ++ rfn ++ " = " ++ val) $
            Q.field_write vs rn' fn' val'

    process :: Q.Valid_state -> String -> IO Q.Valid_state
    process vs rn = do
        let rn' = recordId rn
            vs' = enqueueEvent vs 0 (Q.IProcess rn')
            (vs'', oes) = runStateLoop vs' 0
        forM oes $ \oe ->
            case oe of
                Q.OScheduleCallback delay rn ops ->
                    putStrLn $ "Scheduled callback for " ++ recordNames !! fromInteger rn ++
                        " after " ++ show delay ++ " ticks"
                Q.OHwWrite rn val ->
                    putStrLn $ "Wrote analog out: " ++ recordNames !! fromInteger rn ++
                        " = " ++ show val
                Q.OTraceInput (Q.IProcess rn) -> do
                    putStrLn $ "Handle: process " ++ recordNames !! fromInteger rn
                Q.OTraceInput (Q.IRunCallback rn _) -> do
                    putStrLn $ "Handle: callback " ++ recordNames !! fromInteger rn
                Q.OTraceBegin rn rs -> do
                    putStrLn $ "Begin processing: " ++ recordNames !! fromInteger rn
                    --dumpRecord rs
                Q.OTraceEnd rn rs -> do
                    putStrLn $ "Done processing: " ++ recordNames !! fromInteger rn
                    dumpRecord rs
        return vs''

dumpRecord rs = do
    putStrLn "Fields:"
    mapM_ (dumpRecordField rs) allFields
    putStrLn "End of fields"

dumpRecordField rs fn = case Q.read_field rs fn of
    Nothing -> return ()
    Just (Q.VDouble x) -> putStrLn $ "" ++ show fn ++ " = " ++ show x
    Just (Q.VEnum _ x) -> putStrLn $ "" ++ show fn ++ " = " ++ show x
    Just (Q.VString x) -> putStrLn $ "" ++ show fn ++ " = " ++ conv x   -- no escaping/quotes
    Just (Q.VLong x) -> putStrLn $ "" ++ show fn ++ " = " ++ show x



-- Additional entry points used by abstract interpreter

hldbConfig :: HL.HlDatabase -> Q.Database_config
hldbConfig = conv

hldbState :: HL.HlDatabase -> Q.Database_state
hldbState = conv

hldbProgram :: HL.HlDatabase -> Q.Database_program
hldbProgram hldb =
    case Q.compile_dbp $ hldbConfig hldb of
        Left x -> x
        Right err -> error $
            showTypeError (hldbNameMap hldb) "failed to compile config to a program: " err

hldbNameMap :: HL.HlDatabase -> M.Map Int String
hldbNameMap hldb = M.fromList $ zip [0..] (M.keys hldb)

hldbNameToId :: HL.HlDatabase -> M.Map String Integer
hldbNameToId hldb =
    let baseMap = M.fromList $ zip (M.keys hldb) [0..]
        aliasPairs = do
            (name, r) <- M.toList hldb
            alias <- r ^. HL.hlr_aliases
            return (name, alias)
    in foldl (\m (name, alias) -> M.insert alias (m M.! name) m) baseMap aliasPairs


reportRecordName :: M.Map Int String -> Integer -> String
reportRecordName nameMap rn =
    case M.lookup (fromIntegral rn) nameMap of
        Just name -> name
        Nothing -> "[record " ++ show rn ++ "]"

reportTypeError nameMap (Q.TyENoSuchRecord rn) =
    ["no such record: " ++ reportRecordName nameMap rn]
reportTypeError nameMap (Q.TyENoTypedField fns ty) =
    ["no `" ++ show ty ++ "` entry in `" ++ show fns ++ "`"]
reportTypeError nameMap (Q.TyEInContext ctx e) =
    map (\msg -> reportTypeErrorContext nameMap ctx ++ ": " ++ msg)
        (reportTypeError nameMap e)
reportTypeError nameMap (Q.TyEMultipleErrors e1 e2) =
    reportTypeError nameMap e1 ++ reportTypeError nameMap e2

reportTypeErrorContext nameMap (Q.TCtxRecord rn) =
    "in record " ++ reportRecordName nameMap rn
reportTypeErrorContext nameMap (Q.TCtxOpcode uop) =
    "in opcode `" ++ show uop ++ "`"

reportWfError nameMap (Q.WfeNoSuchRecord rn) =
    ["no such record: " ++ reportRecordName nameMap rn]
reportWfError nameMap (Q.WfeNoSuchField rt fn ft) =
    ["no field `" ++ show fn ++ "` of type `" ++ show ft ++ "` " ++
     "in record of type `" ++ show rt ++ "`"]
reportWfError nameMap (Q.WfeNotConvertible ty1 ty2) =
    ["type `" ++ show ty1 ++ "` is not convertible to `" ++ show ty2 ++ "`"]
reportWfError nameMap (Q.WfeMultipleErrors e1 e2) =
    reportWfError nameMap e1 ++ reportWfError nameMap e2
reportWfError nameMap (Q.WfeInContext ctx e) =
    map (\msg -> reportWfErrorContext nameMap ctx ++ ": " ++ msg)
        (reportWfError nameMap e)
reportWfError nameMap (Q.WfeWrongRecordType actual expected) =
    ["wrong record type: expected `" ++ show expected ++ "`, got `" ++ show actual ++ "`"]
reportWfError nameMap (Q.WfeWrongFieldName actual expected) =
    ["wrong field name: expected `" ++ show expected ++ "`, got `" ++ show actual ++ "`"]
reportWfError nameMap (Q.WfeBadExpr) =
    ["invalid calculation expression"]

reportWfErrorContext nameMap (Q.CtxRecord rn) =
    "in record " ++ reportRecordName nameMap rn
reportWfErrorContext nameMap (Q.CtxOpcode op) =
    "in opcode `" ++ show op ++ "`"
reportWfErrorContext nameMap (Q.CtxField fn) =
    "in field `" ++ show fn ++ "`"
reportWfErrorContext nameMap (Q.CtxTargetRecord rn) =
    "regarding record " ++ reportRecordName nameMap rn

reportTimeError nameMap (Just times) =
    map (\((rn, t1), t2) ->
        reportRecordName nameMap rn ++ ": time increase: " ++ show (t2 - t1)) times
reportTimeError nameMap Nothing =
    ["no times in ETime??"]

reportError nameMap (Q.EWf e) = reportWfError nameMap e
reportError nameMap (Q.ETy e) = reportTypeError nameMap e
reportError nameMap (Q.ETime e) = reportTimeError nameMap e
reportError nameMap (Q.EMsg s) = [conv s]

showError nameMap prefix err =
    let errStrs = reportError nameMap err in
    intercalate "\n" $ prefix : errStrs ++ ["(" ++ show (length errStrs) ++ " total errors)"]
showTypeError nameMap prefix err = intercalate "\n" $ prefix : reportTypeError nameMap err




-- TODO: remove this
compileHldb = hldbProgram

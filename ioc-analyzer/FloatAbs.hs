{-# LANGUAGE CPP, TemplateHaskell, DataKinds, Rank2Types, FlexibleContexts #-}
module FloatAbs
where

import Control.Lens hiding ((^.), use, op)
import Control.Monad hiding (join)
import Control.Monad.State hiding (join)
import qualified Data.Map as M
import Data.Maybe

import qualified CalcExp as CE
import Multi
import qualified HL
import HL (letterToIndex, charToIndex, indexToLetter, indexToChar, idx,
    (^.), use, HlRecordType(..))
import Record
import qualified ToExtraction
import qualified Query as Q

import Debug.Trace

data Abs = Unused Int | IntRange Int Int | Top
  deriving (Eq, Show)

join (Unused a) (Unused b)
  | a == b = Unused a
  | otherwise = IntRange (min a b) (max a b)
join (Unused a) b = join (IntRange a a) b
join a (Unused b) = join a (IntRange b b)
join (IntRange a1 b1) (IntRange a2 b2) = IntRange (min a1 a2) (max b1 b2)
join _ _ = Top

zipAbs f (IntRange a1 b1) (IntRange a2 b2) = IntRange (f a1 a2) (f b1 b2)
zipAbs _ _ _ = Top

isUnused (Unused _) = True
isUnused _ = False

convertUnused (Unused x) = IntRange x x
convertUnused x = x


evalLit x =
    if fromIntegral (floor x :: Int) == x
        then IntRange (floor x) (floor x)
        else Top

makeUnused :: Double -> Abs
makeUnused x = 
    if fromIntegral (floor x :: Int) == x
        then Unused (floor x)
        else Top


data AbsRecord =
      Calc
      { _calc_A_to_L :: Multi 12 Abs
      , _calc_VAL :: Abs
      }
    | CalcOut
      { _calcout_A_to_L :: Multi 12 Abs
      , _calcout_VAL :: Abs
      , _calcout_PVAL :: Abs
      , _calcout_OVAL :: Abs
      , _calcout_tmp0 :: Abs
      }
    | StrCalcOut
      { _scalcout_A_to_L :: Multi 12 Abs
      , _scalcout_VAL :: Abs
      , _scalcout_PVAL :: Abs
      , _scalcout_OVAL :: Abs
      , _scalcout_tmp0 :: Abs
      }
    | ArrayCalcOut
      { _acalcout_A_to_L :: Multi 12 Abs
      , _acalcout_VAL :: Abs
      , _acalcout_PVAL :: Abs
      , _acalcout_OVAL :: Abs
      , _acalcout_tmp0 :: Abs
      }

    | AnalogIn
      { _ai_VAL :: Abs
      }
    | AnalogOut
      { _ao_VAL :: Abs
      , _ao_PVAL :: Abs
      }
    | BinaryIn
      { _bi_VAL :: Abs
      }
    | BinaryOut
      { _bo_VAL :: Abs
      }
    | MBBO
      { _mbbo_VAL :: Abs
      }
    | StringIn {}
    | StringOut {}
    | LongIn
      { _longin_VAL :: Abs
      }
    | LongOut
      { _longout_VAL :: Abs
      }

    | Waveform {}
    | SubArray {}

    | Fanout {}
    | DFanout
      { _dfanout_VAL :: Abs
      }
    | Seq
      { _seq_DO1_to_DOA :: Multi 10 Abs
      }
    | Asyn {}
    | Havoc
  deriving (Eq, Show)
makeLenses ''AbsRecord



makeAbsRecord' r@(HL.Calc {}) = Calc
    { _calc_A_to_L = multiMap makeUnused $ HL._calc_A_to_L r
    , _calc_VAL = makeUnused $ HL._calc_VAL r
    }
makeAbsRecord' r@(HL.CalcOut {}) = CalcOut
    { _calcout_A_to_L = multiMap makeUnused $ HL._calcout_A_to_L r
    , _calcout_VAL = makeUnused $ HL._calcout_VAL r
    , _calcout_OVAL = makeUnused $ HL._calcout_OVAL r
    , _calcout_PVAL = Unused 0
    , _calcout_tmp0 = Unused 0
    }
makeAbsRecord' r@(HL.StrCalcOut {}) = StrCalcOut
    { _scalcout_A_to_L = multiMap makeUnused $ HL._scalcout_A_to_L r
    , _scalcout_VAL = makeUnused $ HL._scalcout_VAL r
    , _scalcout_OVAL = makeUnused $ HL._scalcout_OVAL r
    , _scalcout_PVAL = Unused 0
    , _scalcout_tmp0 = Unused 0
    }
makeAbsRecord' r@(HL.ArrayCalcOut {}) = ArrayCalcOut
    { _acalcout_A_to_L = multiMap makeUnused $ HL._acalcout_A_to_L r
    , _acalcout_VAL = makeUnused $ HL._acalcout_VAL r
    , _acalcout_OVAL = makeUnused $ HL._acalcout_OVAL r
    , _acalcout_PVAL = Unused 0
    , _acalcout_tmp0 = Unused 0
    }

makeAbsRecord' r@(HL.AnalogIn {}) = AnalogIn
    { _ai_VAL = makeUnused $ HL._ai_VAL r
    }
makeAbsRecord' r@(HL.AnalogOut {}) = AnalogOut
    { _ao_VAL = makeUnused $ HL._ao_VAL r
    , _ao_PVAL = makeUnused 0
    }
makeAbsRecord' r@(HL.BinaryIn {}) = BinaryIn
    { _bi_VAL = Unused $ HL._bi_VAL r
    }
makeAbsRecord' r@(HL.BinaryOut {}) = BinaryOut
    { _bo_VAL = Unused $ HL._bo_VAL r
    }
makeAbsRecord' r@(HL.MBBO {}) = MBBO
    { _mbbo_VAL = Unused $ HL._mbbo_VAL r
    }
makeAbsRecord' r@(HL.StringIn {}) = StringIn {}
makeAbsRecord' r@(HL.StringOut {}) = StringOut {}
makeAbsRecord' r@(HL.LongIn {}) = LongIn
    { _longin_VAL = Unused $ fromIntegral $ HL._longin_VAL r
    }
makeAbsRecord' r@(HL.LongOut {}) = LongOut
    { _longout_VAL = Unused $ fromIntegral $ HL._longout_VAL r
    }

makeAbsRecord' r@(HL.Waveform {}) = Waveform {}
makeAbsRecord' r@(HL.SubArray {}) = SubArray {}

makeAbsRecord' r@(HL.Fanout {}) = Fanout {}
makeAbsRecord' r@(HL.DFanout {}) = DFanout
    { _dfanout_VAL = makeUnused $ HL._dfanout_VAL r
    }
makeAbsRecord' r@(HL.Seq {}) = Seq
    { _seq_DO1_to_DOA = multiMap makeUnused $ HL._seq_DO1_to_DOA r
    }
makeAbsRecord' r@(HL.Asyn {}) = Asyn {}

makeAbsRecord' r@(HL.Havoc {}) = Havoc

-- NB: this is specific to Jon's code.  Other codebases may use different ASG
-- rules (consult the .acf file)
handleAsg "DEFAULT" a = a
handleAsg _ a = foldl (\r fn -> writeField r fn Top) a fns
  where
    fieldMap = absFieldMap M.! absRecordType a
        -- Need to indicate a concrete Applicative instance
        :: M.Map String ((Abs -> Identity Abs) -> (AbsRecord -> Identity AbsRecord))
    fns = M.keys fieldMap

makeAbsRecord r =
    let a = makeAbsRecord' (r ^. HL.detail)
        a' = handleAsg (r ^. HL.hlr_ASG) a
    in a'

makeAbsDatabase hldb = M.map makeAbsRecord hldb


type AbsDatabase = M.Map String AbsRecord


absField :: Applicative f => AbsRecord -> String ->
    Maybe ((Abs -> f Abs) -> (AbsRecord -> f AbsRecord))
absField r fn = do
    fields <- M.lookup (absRecordType r) absFieldMap
    M.lookup fn fields

lowerMbboVal Top = IntRange 0 15
lowerMbboVal x = x

lowerBoVal Top = IntRange 0 1
lowerBoVal x = x

readField :: AbsRecord -> String -> Abs
readField r f
  | Just l <- absField r f = r ^. l
  | otherwise = Top

writeFieldRaw :: AbsRecord -> String -> Abs -> AbsRecord
writeFieldRaw r f x
  | Just l <- absField r f = r & l %~ join x
  | otherwise = r

writeField :: AbsRecord -> String -> Abs -> AbsRecord
writeField r@(BinaryOut {}) "VAL" x = writeFieldRaw r "VAL" (lowerBoVal x)
writeField r@(MBBO {}) "VAL" x = writeFieldRaw r "VAL" (lowerMbboVal x)
writeField r f x = writeFieldRaw r f x

readLink :: FieldLink -> AbsDatabase -> Maybe Abs
readLink NoLink _ = Nothing
readLink (Constant x) db = Just $ evalLit x
readLink lnk@(FieldLink {}) db | Just r <- M.lookup (fl_record lnk) db =
    Just $ readField r (fl_field lnk)
readLink _ _ = Just Top

readLink' :: FieldLink -> Abs -> AbsDatabase -> Abs
readLink' l x db = fromMaybe x $ readLink l db

writeLink :: FieldLink -> Abs -> AbsDatabase -> AbsDatabase
writeLink lnk@(FieldLink {}) x db =
    M.adjust (\r -> writeField r (fl_field lnk) x) (fl_record lnk) db
writeLink _ _ db = db



absrec :: forall f. (Functor f) => String ->
    (AbsRecord -> f AbsRecord) -> (AbsDatabase -> f AbsDatabase)
absrec name = lens (\db -> db M.! name) (\db r -> M.insert name r db)

process name hl a@Calc{} = do
    error "NYI: FloatAbs.process Calc"
    {-
    a2l_0 <- use $ absrec name . calc_A_to_L
    -- Read input links
    forM_ [0 .. 11] $ \i -> do
        let inpa = multiGet (hl ^. HL.calc_INPA_to_INPL) i
        a <- use $ absrec name . calc_A_to_L . idx i
        a' <- gets $ readLink' inpa a
        absrec name . calc_A_to_L . idx i %= join a'
    -- Update fields
    a2l <- use $ absrec name . calc_A_to_L
    let op = hl ^. HL.calc_CALC
    let (val', a2l') = evalOp (fromMulti a2l) op
    absrec name . calc_VAL %= join val'
    absrec name . calc_A_to_L %= toMulti . zipWith join a2l' . fromMulti
    return ()
    -}

process name hl a@CalcOut{} = do
    error "NYI: FloatAbs.process CalcOut"
    {-
    -- Read input links
    forM_ [0 .. 11] $ \i -> do
        let inpa = multiGet (hl ^. HL.calcout_INPA_to_INPL) i
        a <- use $ absrec name . calcout_A_to_L . idx i
        a' <- gets $ readLink' inpa a
        absrec name . calcout_A_to_L . idx i %= join a'
    -- Update fields
    a2l <- use $ absrec name . calcout_A_to_L
    let op1 = hl ^. HL.calcout_CALC
    let (val', a2l') = evalOp (fromMulti a2l) op1
    let op2 = hl ^. HL.calcout_OCAL
    let (oval', a2l'') = evalOp a2l' op2
    absrec name . calcout_VAL %= join val'
    absrec name . calcout_OVAL %= join oval'
    absrec name . calcout_A_to_L %= toMulti . zipWith join a2l'' . fromMulti
    -- Write output link
    let outVal = case hl ^. HL.calcout_DOPT of
            HL.DOpt_UseCALC -> val'
            HL.DOpt_UseOCAL -> oval'
    let out = hl ^. HL.calcout_OUT
    old <- gets $ readLink' out outVal
    modify $ writeLink out outVal
    -}

process name hl a@AnalogOut{} = do
    let dol = hl ^. HL.ao_DOL
        val = a ^. ao_VAL
        --out = hl ^. HL.ao_OUT
    val' <- gets $ readLink' dol val
    absrec name . ao_VAL %= join val'
    --modify $ writeLink out (join val val')
    -- TODO: support ao.OUT (for hw & Soft Channel links)

process name hl a@AnalogIn{} = do
    let inp = hl ^. HL.ai_INP
        val = a ^. ai_VAL
    val' <- gets $ readLink' inp val
    absrec name . ai_VAL %= join val'

process name hl a@BinaryOut{} = do
    let dol = hl ^. HL.bo_DOL
        val = a ^. bo_VAL
    val' <- gets $ readLink' dol val
    absrec name . bo_VAL %= join val'

process name hl a@MBBO{} = do
    let dol = hl ^. HL.mbbo_DOL
        val = a ^. mbbo_VAL
    val' <- gets $ readLink' dol val
    absrec name . mbbo_VAL %= join val'

process name hl a@Fanout{} = do
    return ()

process name hl a@DFanout{} = do
    -- Update fields
    let dol = hl ^. HL.dfanout_DOL
        val = a ^. dfanout_VAL
    val' <- gets $ readLink' dol val
    absrec name . dfanout_VAL %= join val'
    -- Write outputs
    let outa2h = hl ^. HL.dfanout_OUTA_to_OUTH
    forM_ (fromMulti outa2h) $ \lnk ->
        modify $ writeLink lnk val'

process name hl a@Seq{} = do
    forM_ [0 .. 9] $ \i -> do
        -- Read
        let dol = multiGet (hl ^. HL.seq_DOL1_to_DOLA) i
        x <- use $ absrec name . seq_DO1_to_DOA . idx i
        x' <- gets $ readLink' dol x
        absrec name . seq_DO1_to_DOA . idx i %= join x'
        -- Write
        let lnk = hl ^. HL.seq_LNK1_to_LNKA . idx i
        y <- use $ absrec name . seq_DO1_to_DOA . idx i
        modify $ writeLink lnk y

process name hl a@Havoc{} = do
    let out_links = hl ^. HL.havoc_out_links
    forM_ out_links $ \lnk ->
        modify $ writeLink lnk Top

processDatabase :: HL.HlDatabase -> AbsDatabase -> AbsDatabase
processDatabase hldb adb = flip execState adb $ do
    forM_ (M.keys adb) $ \name -> do
        process name ((hldb M.! name) ^. HL.detail) (adb M.! name)



#ifndef NO_COQ

convertAbs (Unused i) = Just (fromIntegral i, fromIntegral i)
convertAbs (IntRange a b) = Just (fromIntegral a, fromIntegral b)
convertAbs Top = Nothing

convertAbsRecord a =
    let conv = convertAbs in
    case a of
        Fanout{} ->
            Q.RaFanout $ Q.FanoutAbs
        AnalogIn{} ->
            Q.RaAnalogIn $ {-Q.AnalogInAbs-} (conv $ a ^. ai_VAL)
        AnalogOut{} ->
            Q.RaAnalogOut $ Q.AnalogOutAbs (conv $ a ^. ao_VAL) ({- PVAL -} conv $ a ^. ao_VAL)
        DFanout{} ->
            Q.RaDFanout $ {-Q.DFanoutAbs-} (conv $ a ^. dfanout_VAL)

convertAbsDatabase :: AbsDatabase -> Q.Database_abs
convertAbsDatabase abs = map (convertAbsRecord . snd) $ M.toList abs

validate :: HL.HlDatabase -> AbsDatabase -> AbsDatabase
validate hldb dba =
    let dba' = convertAbsDatabase dba
        dbp = ToExtraction.compileHldb hldb
    in case Q.check_database_program dba' dbp of
        Left _ -> dba
        Right errs -> error $ "abstract interpretation failed: " ++ show errs

runAnalysis :: HL.HlDatabase -> AbsDatabase
runAnalysis hldb = validate hldb $ go 100 (makeAbsDatabase hldb)
  where
    go 0 adb = adb
    go n adb =
        let adb' = processDatabase hldb adb
        in if adb == adb' then adb' else go (n - 1) adb'

#else

runAnalysis :: HL.HlDatabase -> AbsDatabase
runAnalysis hldb = go 100 (makeAbsDatabase hldb)
  where
    go 0 adb = adb
    go n adb =
        let adb' = processDatabase hldb adb
        in if adb == adb' then adb' else go (n - 1) adb'

#endif


type Report = [(String, String, Int, Int)]

report :: AbsDatabase -> Report
report adb = concatMap (\(k,v) -> reportRecord k v) $ M.toList adb

reportRecord :: String -> AbsRecord -> Report
reportRecord rn r =
    concatMap (\(l, fn) -> reportAbs rn fn (r ^. l)) (reportFields r)

absFieldList :: Applicative f =>
    [(HlRecordType, [(String, (Abs -> f Abs) -> (AbsRecord -> f AbsRecord))])]
absFieldList =
    [(RtCalc,
        map (\i -> ([indexToLetter i], calc_A_to_L . idx i)) [0..11] ++
        [("VAL", calc_VAL)])
    ,(RtAnalogOut, [("VAL", ao_VAL)])
    ,(RtAnalogIn, [("VAL", ai_VAL)])
    ,(RtCalcOut,
        map (\i -> ([indexToLetter i], calcout_A_to_L . idx i)) [0..11] ++
        [("VAL", calcout_VAL), ("OVAL", calcout_OVAL)])
    ,(RtBinaryOut, [("VAL", bo_VAL)])
    ,(RtMBBO, [("VAL", mbbo_VAL)])
    ,(RtFanout, [])
    ,(RtDFanout, [("VAL", dfanout_VAL)])
    ,(RtSeq,
        map (\i -> ("DO" ++ [indexToChar i], seq_DO1_to_DOA . idx i)) [0..9])
    ,(RtHavoc, [])
    ]

absFieldMap :: Applicative f =>
    M.Map HlRecordType (M.Map String ((Abs -> f Abs) -> (AbsRecord -> f AbsRecord)))
absFieldMap =
    M.fromList [(rty, fieldMap) | (rty, fields) <- absFieldList,
        fieldMap <- [M.fromList fields]
    ]

absRecordType :: AbsRecord -> HlRecordType
absRecordType Calc{} = RtCalc
absRecordType AnalogOut{} = RtAnalogOut
absRecordType AnalogIn{} = RtAnalogIn
absRecordType CalcOut{} = RtCalcOut
absRecordType BinaryOut{} = RtBinaryOut
absRecordType MBBO{} = RtMBBO
absRecordType Fanout{} = RtFanout
absRecordType DFanout{} = RtDFanout
absRecordType Seq{} = RtSeq
absRecordType Havoc{} = RtHavoc

reportFields r = map (\(a,b) -> (b,a)) $ M.toList $ absFieldMap M.! absRecordType r

reportAbs :: String -> String -> Abs -> Report
reportAbs rn fn (IntRange min max) = [(rn, fn, min, max)]
reportAbs _ _ _ = []

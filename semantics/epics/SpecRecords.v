Require Import Arith.
Require Import List.
Import ListNotations.

Require Import v1.Multi.
Require Import v1.Util.
Require Import epics.SpecTypes.
Require Import epics.SpecRecordData.
Require Import epics.SpecRecordSetters.


(* database info *)

Inductive record : Set :=
| Calc :            calc_config ->              calc_state ->               record
| CalcOut :         calc_out_config ->          calc_out_state ->           record
| StrCalcOut :      str_calc_out_config ->      str_calc_out_state ->       record
| ArrayCalcOut n :  array_calc_out_config n ->  array_calc_out_state n ->   record
| Fanout :          fanout_config ->            fanout_state ->             record
| AnalogIn :        analog_in_config ->         analog_in_state ->          record
| AnalogOut :       analog_out_config ->        analog_out_state ->         record
| BinaryIn :        binary_in_config ->         binary_in_state ->          record
| BinaryOut :       binary_out_config ->        binary_out_state ->         record
| MBBO :            mbbo_config ->              mbbo_state ->               record
| StringIn :        string_in_config ->         string_in_state ->          record
| StringOut :       string_out_config ->        string_out_state ->         record
| LongIn :          long_in_config ->           long_in_state ->            record
| LongOut :         long_out_config ->          long_out_state ->           record
| DFanout :         dfanout_config ->           dfanout_state ->            record
| Seq :             seq_config ->               seq_state ->                record
| Waveform ty n :   waveform_config ty n ->     waveform_state ty n ->      record
| Subarray ty n m : subarray_config ty n m ->   subarray_state ty n m ->    record
| Asyn :            asyn_config ->              asyn_state ->               record
.

Definition database := list record.


Inductive record_config : Set :=
| RcCalc :          calc_config -> record_config
| RcCalcOut :       calc_out_config -> record_config
| RcStrCalcOut :    str_calc_out_config -> record_config
| RcArrayCalcOut n : array_calc_out_config n -> record_config
| RcFanout :        fanout_config -> record_config
| RcAnalogIn :      analog_in_config -> record_config
| RcAnalogOut :     analog_out_config -> record_config
| RcBinaryIn :      binary_in_config -> record_config
| RcBinaryOut :     binary_out_config -> record_config
| RcMBBO :          mbbo_config -> record_config
| RcStringIn :      string_in_config -> record_config
| RcStringOut :     string_out_config -> record_config
| RcLongIn :        long_in_config -> record_config
| RcLongOut :       long_out_config -> record_config
| RcDFanout :       dfanout_config -> record_config
| RcSeq :           seq_config -> record_config
| RcWaveform ty n : waveform_config ty n -> record_config
| RcSubarray ty n m : subarray_config ty n m -> record_config
| RcAsyn :          asyn_config -> record_config
.

Inductive record_state : Set :=
| RsCalc :          calc_state -> record_state
| RsCalcOut :       calc_out_state -> record_state
| RsStrCalcOut :    str_calc_out_state -> record_state
| RsArrayCalcOut n : array_calc_out_state n -> record_state
| RsFanout :        fanout_state -> record_state
| RsAnalogIn :      analog_in_state -> record_state
| RsAnalogOut :     analog_out_state -> record_state
| RsBinaryIn :      binary_in_state -> record_state
| RsBinaryOut :     binary_out_state -> record_state
| RsMBBO :          mbbo_state -> record_state
| RsStringIn :      string_in_state -> record_state
| RsStringOut :     string_out_state -> record_state
| RsLongIn :        long_in_state -> record_state
| RsLongOut :       long_out_state -> record_state
| RsDFanout :       dfanout_state -> record_state
| RsSeq :           seq_state -> record_state
| RsWaveform ty n : waveform_state ty n -> record_state
| RsSubarray ty n m : subarray_state ty n m -> record_state
| RsAsyn :          asyn_state -> record_state
.

Definition database_config := list record_config.
Definition database_state := list record_state.

Notation lookup_state := (@lookup record_state).
Notation lookup_config := (@lookup record_config).


Inductive record_type : Set :=
| RtCalc
| RtCalcOut
| RtStrCalcOut
| RtArrayCalcOut (n : nat)
| RtFanout
| RtDFanout
| RtSeq
| RtAnalogIn
| RtAnalogOut
| RtBinaryIn
| RtBinaryOut
| RtMBBO
| RtStringIn
| RtStringOut
| RtLongIn
| RtLongOut
| RtWaveform (ty : elem_type) (n : nat)
| RtSubarray (ty : elem_type) (n m : nat)
| RtAsyn
.

Definition record_type_eq_dec (a b : record_type) : {a = b} + {a <> b}.
decide equality; eauto using eq_nat_dec, elem_type_eq_dec.
Defined.

Definition database_type := list record_type.

Notation lookup_type := (@lookup record_type).

Definition record_state_type rs :=
    match rs with
    | RsCalc _ => RtCalc
    | RsCalcOut _ => RtCalcOut
    | RsStrCalcOut _ => RtStrCalcOut
    | RsArrayCalcOut n _ => RtArrayCalcOut n
    | RsFanout _ => RtFanout
    | RsDFanout _ => RtDFanout
    | RsSeq _ => RtSeq
    | RsAnalogIn _ => RtAnalogIn
    | RsAnalogOut _ => RtAnalogOut
    | RsBinaryIn _ => RtBinaryIn
    | RsBinaryOut _ => RtBinaryOut
    | RsMBBO _ => RtMBBO
    | RsStringIn _ => RtStringIn
    | RsStringOut _ => RtStringOut
    | RsLongIn _ => RtLongIn
    | RsLongOut _ => RtLongOut
    | RsWaveform ty n _ => RtWaveform ty n
    | RsSubarray ty n m _ => RtSubarray ty n m
    | RsAsyn _ => RtAsyn
    end.

Definition record_config_type rc :=
    match rc with
    | RcCalc _ => RtCalc
    | RcCalcOut _ => RtCalcOut
    | RcStrCalcOut _ => RtStrCalcOut
    | RcArrayCalcOut n _ => RtArrayCalcOut n
    | RcFanout _ => RtFanout
    | RcDFanout _ => RtDFanout
    | RcSeq _ => RtSeq
    | RcAnalogIn _ => RtAnalogIn
    | RcAnalogOut _ => RtAnalogOut
    | RcBinaryIn _ => RtBinaryIn
    | RcBinaryOut _ => RtBinaryOut
    | RcMBBO _ => RtMBBO
    | RcStringIn _ => RtStringIn
    | RcStringOut _ => RtStringOut
    | RcLongIn _ => RtLongIn
    | RcLongOut _ => RtLongOut
    | RcWaveform ty n _ => RtWaveform ty n
    | RcSubarray ty n m _ => RtSubarray ty n m
    | RcAsyn _ => RtAsyn
    end.

Definition database_config_type dbc :=
    map record_config_type dbc.

Definition database_state_type dbs :=
    map record_state_type dbs.


Definition read_field rs fn : option value :=
    match fn, rs with
    | f_A_to_L i,   RsCalc st => Some (VDouble (calc_A_to_L st !! i))
    | f_VAL,        RsCalc st => Some (VDouble (calc_VAL st))

    | f_A_to_L i,   RsCalcOut st => Some (VDouble (calc_out_A_to_L st !! i))
    | f_VAL,        RsCalcOut st => Some (VDouble (calc_out_VAL st))
    | f_PVAL,       RsCalcOut st => Some (VDouble (calc_out_PVAL st))
    | f_OVAL,       RsCalcOut st => Some (VDouble (calc_out_OVAL st))
    | f_tmp0,       RsCalcOut st => Some (VDouble (calc_out_tmp0 st))

    | f_A_to_L i,   RsStrCalcOut st => Some (VDouble (str_calc_out_A_to_L st !! i))
    | f_AA_to_LL i, RsStrCalcOut st => Some (VString (str_calc_out_AA_to_LL st !! i))
    | f_VAL,        RsStrCalcOut st => Some (VDouble (str_calc_out_VAL st))
    | f_SVAL,       RsStrCalcOut st => Some (VString (str_calc_out_SVAL st))
    | f_PVAL,       RsStrCalcOut st => Some (VDouble (str_calc_out_PVAL st))
    | f_OVAL,       RsStrCalcOut st => Some (VDouble (str_calc_out_OVAL st))
    | f_OSV,        RsStrCalcOut st => Some (VString (str_calc_out_OSV st))
    | f_tmp0,       RsStrCalcOut st => Some (VDouble (str_calc_out_tmp0 st))

    | f_A_to_L i,   RsArrayCalcOut n st => Some (VDouble (array_calc_out_A_to_L st !! i))
    | f_AA_to_LL i, RsArrayCalcOut n st => Some (VArray (array_calc_out_AA_to_LL st !! i))
    | f_VAL,        RsArrayCalcOut n st => Some (VDouble (array_calc_out_VAL st))
    | f_AVAL,       RsArrayCalcOut n st => Some (VArray (array_calc_out_AVAL st))
    | f_PVAL,       RsArrayCalcOut n st => Some (VDouble (array_calc_out_PVAL st))
    | f_OVAL,       RsArrayCalcOut n st => Some (VDouble (array_calc_out_OVAL st))
    | f_OAV,        RsArrayCalcOut n st => Some (VArray (array_calc_out_OAV st))
    | f_tmp0,       RsArrayCalcOut n st => Some (VDouble (array_calc_out_tmp0 st))

    | f_VAL,        RsDFanout st => Some (VDouble (dfanout_VAL st))

    | f_DO1_to_DOA i, RsSeq st => Some (VDouble (seq_DO1_to_DOA st !! i))
    | f_PACT,       RsSeq st => Some (VEnum (seq_PACT st))

    | f_VAL,        RsAnalogIn st => Some (VDouble (analog_in_VAL st))
    | f_VAL,        RsAnalogOut st => Some (VDouble (analog_out_VAL st))
    | f_PVAL,       RsAnalogOut st => Some (VDouble (analog_out_PVAL st))

    | f_VAL,        RsBinaryIn st => Some (VEnum (binary_in_VAL st))
    | f_VAL,        RsBinaryOut st => Some (VEnum (binary_out_VAL st))

    | f_VAL,        RsMBBO st => Some (VEnum (mbbo_VAL st))

    | f_VAL,        RsStringIn st => Some (VString (string_in_VAL st))
    | f_VAL,        RsStringOut st => Some (VString (string_out_VAL st))

    | f_VAL,        RsLongIn st => Some (VLong (long_in_VAL st))
    | f_VAL,        RsLongOut st => Some (VLong (long_out_VAL st))

    | f_VAL,        RsWaveform _ _ st => Some (VArray (waveform_VAL st))

    | f_VAL,        RsSubarray _ _ _ st => Some (VArray (subarray_VAL st))
    | f_tmp0,       RsSubarray _ _ _ st => Some (VArray (subarray_tmp0 st))

    | _, _ => None
    end.

Definition write_field rs fn x : option record_state :=
    match fn, rs with
    | f_A_to_L i, RsCalc st =>
            unwrap_double x >>= fun x =>
            let a2l' := multi_set (calc_A_to_L st) i x in
            Some (RsCalc (set_calc_A_to_L st a2l'))
    | f_VAL,      RsCalc st =>
            unwrap_double x >>= fun x => Some (RsCalc (set_calc_VAL st x))

    | f_A_to_L i, RsCalcOut st =>
            unwrap_double x >>= fun x =>
            let a2l' := multi_set (calc_out_A_to_L st) i x in
            Some (RsCalcOut (set_calc_out_A_to_L st a2l'))
    | f_VAL,      RsCalcOut st =>
            unwrap_double x >>= fun x => Some (RsCalcOut (set_calc_out_VAL st x))
    | f_PVAL,     RsCalcOut st =>
            unwrap_double x >>= fun x => Some (RsCalcOut (set_calc_out_PVAL st x))
    | f_OVAL,     RsCalcOut st =>
            unwrap_double x >>= fun x => Some (RsCalcOut (set_calc_out_OVAL st x))
    | f_tmp0,     RsCalcOut st =>
            unwrap_double x >>= fun x => Some (RsCalcOut (set_calc_out_tmp0 st x))

    | f_A_to_L i, RsStrCalcOut st =>
            unwrap_double x >>= fun x =>
            let a2l' := multi_set (str_calc_out_A_to_L st) i x in
            Some (RsStrCalcOut (set_str_calc_out_A_to_L st a2l'))
    | f_AA_to_LL i, RsStrCalcOut st =>
            unwrap_string x >>= fun x =>
            let a2l' := multi_set (str_calc_out_AA_to_LL st) i x in
            Some (RsStrCalcOut (set_str_calc_out_AA_to_LL st a2l'))
    | f_VAL,      RsStrCalcOut st =>
            unwrap_double x >>= fun x => Some (RsStrCalcOut (set_str_calc_out_VAL st x))
    | f_SVAL,      RsStrCalcOut st =>
            unwrap_string x >>= fun x => Some (RsStrCalcOut (set_str_calc_out_SVAL st x))
    | f_PVAL,     RsStrCalcOut st =>
            unwrap_double x >>= fun x => Some (RsStrCalcOut (set_str_calc_out_PVAL st x))
    | f_OVAL,     RsStrCalcOut st =>
            unwrap_double x >>= fun x => Some (RsStrCalcOut (set_str_calc_out_OVAL st x))
    | f_OSV,      RsStrCalcOut st =>
            unwrap_string x >>= fun x => Some (RsStrCalcOut (set_str_calc_out_OSV st x))
    | f_tmp0,     RsStrCalcOut st =>
            unwrap_double x >>= fun x => Some (RsStrCalcOut (set_str_calc_out_tmp0 st x))

    | f_A_to_L i, RsArrayCalcOut n st =>
            unwrap_double x >>= fun x =>
            let a2l' := multi_set (array_calc_out_A_to_L st) i x in
            Some (RsArrayCalcOut _ (set_array_calc_out_A_to_L st a2l'))
    | f_AA_to_LL i, RsArrayCalcOut n st =>
            unwrap_array TeDouble n x >>= fun x =>
            let a2l' := multi_set (array_calc_out_AA_to_LL st) i x in
            Some (RsArrayCalcOut _ (set_array_calc_out_AA_to_LL st a2l'))
    | f_VAL,      RsArrayCalcOut n st =>
            unwrap_double x >>= fun x => Some (RsArrayCalcOut _ (set_array_calc_out_VAL st x))
    | f_AVAL,      RsArrayCalcOut n st =>
            unwrap_array TeDouble n x >>= fun x =>
                Some (RsArrayCalcOut _ (set_array_calc_out_AVAL st x))
    | f_PVAL,     RsArrayCalcOut n st =>
            unwrap_double x >>= fun x => Some (RsArrayCalcOut _ (set_array_calc_out_PVAL st x))
    | f_OVAL,     RsArrayCalcOut n st =>
            unwrap_double x >>= fun x => Some (RsArrayCalcOut _ (set_array_calc_out_OVAL st x))
    | f_OAV,      RsArrayCalcOut n st =>
            unwrap_array TeDouble n x >>= fun x =>
                Some (RsArrayCalcOut _ (set_array_calc_out_OAV st x))
    | f_tmp0,     RsArrayCalcOut n st =>
            unwrap_double x >>= fun x => Some (RsArrayCalcOut _ (set_array_calc_out_tmp0 st x))

    | f_VAL,      RsDFanout st =>
            unwrap_double x >>= fun x => Some (RsDFanout (set_dfanout_VAL st x))

    | f_DO1_to_DOA i, RsSeq st =>
            unwrap_double x >>= fun x =>
            let do' := multi_set (seq_DO1_to_DOA st) i x in
            Some (RsSeq (set_seq_DO1_to_DOA st do'))
    | f_PACT,     RsSeq st =>
            unwrap_enum x >>= fun x => Some (RsSeq (set_seq_PACT st x))

    | f_VAL,      RsAnalogIn st =>
            unwrap_double x >>= fun x => Some (RsAnalogIn (set_analog_in_VAL st x))
    | f_VAL,      RsAnalogOut st =>
            unwrap_double x >>= fun x => Some (RsAnalogOut (set_analog_out_VAL st x))
    | f_PVAL,     RsAnalogOut st =>
            unwrap_double x >>= fun x => Some (RsAnalogOut (set_analog_out_PVAL st x))

    | f_VAL,      RsBinaryIn st =>
            unwrap_enum x >>= fun x => Some (RsBinaryIn (set_binary_in_VAL st x))
    | f_VAL,      RsBinaryOut st =>
            unwrap_enum x >>= fun x => Some (RsBinaryOut (set_binary_out_VAL st x))

    | f_VAL,      RsMBBO st =>
            unwrap_enum x >>= fun x => Some (RsMBBO (set_mbbo_VAL st x))

    | f_VAL,      RsStringIn st =>
            unwrap_string x >>= fun x => Some (RsStringIn (set_string_in_VAL st x))
    | f_VAL,      RsStringOut st =>
            unwrap_string x >>= fun x => Some (RsStringOut (set_string_out_VAL st x))

    | f_VAL,      RsLongIn st =>
            unwrap_long x >>= fun x => Some (RsLongIn (set_long_in_VAL st x))
    | f_VAL,      RsLongOut st =>
            unwrap_long x >>= fun x => Some (RsLongOut (set_long_out_VAL st x))

    | f_VAL,      RsWaveform ty n st =>
            unwrap_array ty n x >>= fun x =>
            Some (RsWaveform _ _ (set_waveform_VAL st x))

    | f_VAL,      RsSubarray ty n m st =>
            unwrap_array ty n x >>= fun x =>
            Some (RsSubarray _ _ _ (set_subarray_VAL st x))
    | f_tmp0,     RsSubarray ty n m st =>
            unwrap_array ty m x >>= fun x =>
            Some (RsSubarray _ _ _ (set_subarray_tmp0 st x))

    | _, _ => None
    end.

(* Total function that returns the type of a field within a record.  If the
   indicated record type has no such field, returns an arbitrary type. *)
Definition record_field_type rt (fn : field_name) : option field_type :=
    match rt, fn with
    | RtCalc, f_A_to_L _ => Some TDouble
    | RtCalc, f_VAL => Some TDouble

    | RtCalcOut, f_A_to_L _ => Some TDouble
    | RtCalcOut, f_VAL => Some TDouble
    | RtCalcOut, f_PVAL => Some TDouble
    | RtCalcOut, f_OVAL => Some TDouble
    | RtCalcOut, f_tmp0 => Some TDouble

    | RtStrCalcOut, f_A_to_L _ => Some TDouble
    | RtStrCalcOut, f_AA_to_LL _ => Some TString
    | RtStrCalcOut, f_VAL => Some TDouble
    | RtStrCalcOut, f_SVAL => Some TString
    | RtStrCalcOut, f_PVAL => Some TDouble
    | RtStrCalcOut, f_OVAL => Some TDouble
    | RtStrCalcOut, f_OSV => Some TString
    | RtStrCalcOut, f_tmp0 => Some TDouble

    | RtArrayCalcOut n, f_A_to_L _ => Some TDouble
    | RtArrayCalcOut n, f_AA_to_LL _ => Some (TArray TeDouble n)
    | RtArrayCalcOut n, f_VAL => Some TDouble
    | RtArrayCalcOut n, f_AVAL => Some (TArray TeDouble n)
    | RtArrayCalcOut n, f_PVAL => Some TDouble
    | RtArrayCalcOut n, f_OVAL => Some TDouble
    | RtArrayCalcOut n, f_OAV => Some (TArray TeDouble n)
    | RtArrayCalcOut n, f_tmp0 => Some TDouble

    (* RtFanout has no fields *)

    | RtAnalogIn, f_VAL => Some TDouble

    | RtAnalogOut, f_VAL => Some TDouble
    | RtAnalogOut, f_PVAL => Some TDouble

    | RtBinaryIn, f_VAL => Some TEnum

    | RtBinaryOut, f_VAL => Some TEnum

    | RtMBBO, f_VAL => Some TEnum

    | RtStringIn, f_VAL => Some TString

    | RtStringOut, f_VAL => Some TString

    | RtLongIn, f_VAL => Some TLong

    | RtLongOut, f_VAL => Some TLong

    | RtDFanout, f_VAL => Some TDouble

    | RtSeq, f_DO1_to_DOA _ => Some TDouble
    | RtSeq, f_PACT => Some TEnum

    | RtWaveform ty n, f_VAL => Some (TArray ty n)

    | RtSubarray ty n m, f_VAL => Some (TArray ty n)
    | RtSubarray ty n m, f_tmp0 => Some (TArray ty m)

    (* RtAsyn has no fields *)

    | _, _ => None
    end.

Fixpoint update_record (f : record_state -> option record_state) dbs (rn : record_name) :
        option database_state :=
    match dbs, rn with
    | [], _ => None
    | rs :: dbs', 0 =>
            match f rs with
            | None => None
            | Some rs' => Some (rs' :: dbs')
            end
    | rs :: dbs', S rn' =>
            match update_record f dbs' rn' with
            | None => None
            | Some dbs'' => Some (rs :: dbs'')
            end
    end.


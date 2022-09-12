Require Import Arith.
Require Import List.
Import ListNotations.

Require Import epics.SpecTypes.
Require Import epics.SpecRecords.


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



Require Import Arith.
Require Import ZArith.
Require Import List.
Import ListNotations.

Require Import v1.NeutronTactics.
Require Import v1.Util.
Require Import v1.Multi.
Require Import v1.Expr.

Require Import v1.EpicsTypes.
Require v1.EpicsRecords.
Require Import v1.FloatAbsBase.


Inductive record_abs : Set :=
| RaCalc :          calc_abs -> record_abs
| RaCalcOut :       calc_out_abs -> record_abs
| RaStrCalcOut :    str_calc_out_abs -> record_abs
| RaArrayCalcOut n : array_calc_out_abs n -> record_abs
| RaFanout :        fanout_abs -> record_abs
| RaAnalogIn :      analog_in_abs -> record_abs
| RaAnalogOut :     analog_out_abs -> record_abs
| RaBinaryIn :      binary_in_abs -> record_abs
| RaBinaryOut :     binary_out_abs -> record_abs
| RaMBBO :          mbbo_abs -> record_abs
| RaStringIn :      string_in_abs -> record_abs
| RaStringOut :     string_out_abs -> record_abs
| RaLongIn :        long_in_abs -> record_abs
| RaLongOut :       long_out_abs -> record_abs
| RaDFanout :       dfanout_abs -> record_abs
| RaSeq :           seq_abs -> record_abs
| RaWaveform ty n : waveform_abs ty n -> record_abs
| RaSubarray ty n m : subarray_abs ty n m -> record_abs
| RaAsyn :          asyn_abs -> record_abs
.

Definition database_abs := list record_abs.

Notation lookup_abs := (@lookup record_abs).

Definition record_abs_type ra :=
    match ra with
    | RaCalc _ => EpicsRecords.RtCalc
    | RaCalcOut _ => EpicsRecords.RtCalcOut
    | RaStrCalcOut _ => EpicsRecords.RtStrCalcOut
    | RaArrayCalcOut n _ => EpicsRecords.RtArrayCalcOut n
    | RaFanout _ => EpicsRecords.RtFanout
    | RaAnalogIn _ => EpicsRecords.RtAnalogIn
    | RaAnalogOut _ => EpicsRecords.RtAnalogOut
    | RaBinaryIn _ => EpicsRecords.RtBinaryIn
    | RaBinaryOut _ => EpicsRecords.RtBinaryOut
    | RaMBBO _ => EpicsRecords.RtMBBO
    | RaStringIn _ => EpicsRecords.RtStringIn
    | RaStringOut _ => EpicsRecords.RtStringOut
    | RaLongIn _ => EpicsRecords.RtLongIn
    | RaLongOut _ => EpicsRecords.RtLongOut
    | RaDFanout _ => EpicsRecords.RtDFanout
    | RaSeq _ => EpicsRecords.RtSeq
    | RaWaveform ty n _ => EpicsRecords.RtWaveform ty n
    | RaSubarray ty n m _ => EpicsRecords.RtSubarray ty n m
    | RaAsyn _ => EpicsRecords.RtAsyn
    end.

Definition database_abs_type dba :=
    map record_abs_type dba.


Definition read_field ra fn : option abs_value :=
    match fn, ra with
    | f_A_to_L i,   RaCalc st => Some (calc_A_to_L st !! i)
    | f_VAL,        RaCalc st => Some (calc_VAL st)

    | f_A_to_L i,   RaCalcOut st => Some (calc_out_A_to_L st !! i)
    | f_VAL,        RaCalcOut st => Some (calc_out_VAL st)
    | f_PVAL,       RaCalcOut st => Some (calc_out_PVAL st)
    | f_OVAL,       RaCalcOut st => Some (calc_out_OVAL st)
    | f_tmp 0,      RaCalcOut st => Some (calc_out_tmp0 st)

    | f_A_to_L i,   RaStrCalcOut st => Some (str_calc_out_A_to_L st !! i)
    | f_AA_to_LL i, RaStrCalcOut st => Some None
    | f_VAL,        RaStrCalcOut st => Some (str_calc_out_VAL st)
    | f_SVAL,       RaStrCalcOut st => Some None
    | f_PVAL,       RaStrCalcOut st => Some (str_calc_out_PVAL st)
    | f_OVAL,       RaStrCalcOut st => Some (str_calc_out_OVAL st)
    | f_OSV,        RaStrCalcOut st => Some None
    | f_tmp 0,      RaStrCalcOut st => Some (str_calc_out_tmp0 st)

    | f_A_to_L i,   RaArrayCalcOut n st => Some (array_calc_out_A_to_L st !! i)
    | f_AA_to_LL i, RaArrayCalcOut n st => Some None
    | f_VAL,        RaArrayCalcOut n st => Some (array_calc_out_VAL st)
    | f_AVAL,       RaArrayCalcOut n st => Some None
    | f_PVAL,       RaArrayCalcOut n st => Some (array_calc_out_PVAL st)
    | f_OVAL,       RaArrayCalcOut n st => Some (array_calc_out_OVAL st)
    | f_OAV,        RaArrayCalcOut n st => Some None
    | f_tmp 0,      RaArrayCalcOut n st => Some (array_calc_out_tmp0 st)

    | f_VAL,        RaAnalogIn st => Some (analog_in_VAL st)
    | f_VAL,        RaAnalogOut st => Some (analog_out_VAL st)
    | f_PVAL,       RaAnalogOut st => Some (analog_out_PVAL st)

    | f_VAL,        RaBinaryIn st => Some (binary_in_VAL st)
    | f_VAL,        RaBinaryOut st => Some (binary_out_VAL st)

    | f_VAL,        RaMBBO st => Some (mbbo_VAL st)

    | f_VAL,        RaStringIn st => Some None
    | f_VAL,        RaStringOut st => Some None

    | f_VAL,        RaLongIn st => Some (long_in_VAL st)
    | f_VAL,        RaLongOut st => Some (long_out_VAL st)

    | f_VAL,        RaDFanout st => Some (dfanout_VAL st)

    | f_DO1_to_DOA i, RaSeq st => Some (seq_DO1_to_DOA st !! i)
    | f_PACT,       RaSeq st => Some (Some (0, 1)%Z)

    | f_VAL,        RaWaveform ty n st => Some None

    | f_VAL,        RaSubarray ty n m st => Some None
    | f_tmp 0,      RaSubarray ty n m st => Some None

    | _, _ => None
    end.

Definition write_field ra fn x : option record_abs :=
    match fn, ra with
    | f_A_to_L i, RaCalc st =>
            let a2l' := multi_set (calc_A_to_L st) i x in
            Some (RaCalc (set_calc_A_to_L st a2l'))
    | f_VAL,      RaCalc st =>
            Some (RaCalc (set_calc_VAL st x))

    | f_A_to_L i, RaCalcOut st =>
            let a2l' := multi_set (calc_out_A_to_L st) i x in
            Some (RaCalcOut (set_calc_out_A_to_L st a2l'))
    | f_VAL,      RaCalcOut st =>
            Some (RaCalcOut (set_calc_out_VAL st x))
    | f_PVAL,     RaCalcOut st =>
            Some (RaCalcOut (set_calc_out_PVAL st x))
    | f_OVAL,     RaCalcOut st =>
            Some (RaCalcOut (set_calc_out_OVAL st x))
    | f_tmp 0,    RaCalcOut st =>
            Some (RaCalcOut (set_calc_out_tmp0 st x))

    | f_A_to_L i, RaStrCalcOut st =>
            let a2l' := multi_set (str_calc_out_A_to_L st) i x in
            Some (RaStrCalcOut (set_str_calc_out_A_to_L st a2l'))
    | f_AA_to_LL i, RaStrCalcOut st => Some ra
    | f_VAL,      RaStrCalcOut st =>
            Some (RaStrCalcOut (set_str_calc_out_VAL st x))
    | f_SVAL,     RaStrCalcOut st => Some ra
    | f_PVAL,     RaStrCalcOut st =>
            Some (RaStrCalcOut (set_str_calc_out_PVAL st x))
    | f_OVAL,     RaStrCalcOut st =>
            Some (RaStrCalcOut (set_str_calc_out_OVAL st x))
    | f_OSV,      RaStrCalcOut st => Some ra
    | f_tmp 0,    RaStrCalcOut st =>
            Some (RaStrCalcOut (set_str_calc_out_tmp0 st x))

    | f_A_to_L i, RaArrayCalcOut n st =>
            let a2l' := multi_set (array_calc_out_A_to_L st) i x in
            Some (RaArrayCalcOut _ (set_array_calc_out_A_to_L st a2l'))
    | f_AA_to_LL i, RaArrayCalcOut n st => Some ra
    | f_VAL,      RaArrayCalcOut n st =>
            Some (RaArrayCalcOut _ (set_array_calc_out_VAL st x))
    | f_SVAL,     RaArrayCalcOut n st => Some ra
    | f_PVAL,     RaArrayCalcOut n st =>
            Some (RaArrayCalcOut _ (set_array_calc_out_PVAL st x))
    | f_OVAL,     RaArrayCalcOut n st =>
            Some (RaArrayCalcOut _ (set_array_calc_out_OVAL st x))
    | f_OSV,      RaArrayCalcOut n st => Some ra
    | f_tmp 0,    RaArrayCalcOut n st =>
            Some (RaArrayCalcOut _ (set_array_calc_out_tmp0 st x))

    | f_VAL,      RaAnalogIn st =>
            Some (RaAnalogIn (set_analog_in_VAL st x))
    | f_VAL,      RaAnalogOut st =>
            Some (RaAnalogOut (set_analog_out_VAL st x))
    | f_PVAL,     RaAnalogOut st =>
            Some (RaAnalogOut (set_analog_out_PVAL st x))

    | f_VAL,      RaBinaryIn st =>
            Some (RaBinaryIn (set_binary_in_VAL st x))
    | f_VAL,      RaBinaryOut st =>
            Some (RaBinaryOut (set_binary_out_VAL st x))

    | f_VAL,      RaMBBO st =>
            Some (RaMBBO (set_mbbo_VAL st x))

    | f_VAL,      RaStringIn st => Some ra
    | f_VAL,      RaStringOut st => Some ra

    | f_VAL,      RaLongIn st =>
            Some (RaLongIn (set_long_in_VAL st x))
    | f_VAL,      RaLongOut st =>
            Some (RaLongOut (set_long_out_VAL st x))

    | f_VAL,      RaDFanout st =>
            Some (RaDFanout (set_dfanout_VAL st x))

    | f_DO1_to_DOA i, RaSeq st =>
            let dos' := multi_set (seq_DO1_to_DOA st) i x in
            Some (RaSeq (set_seq_DO1_to_DOA st dos'))
    | f_PACT, RaSeq st => Some ra

    | f_VAL,      RaWaveform ty n st => Some ra

    | f_VAL,      RaSubarray ty n m st => Some ra
    | f_tmp 0,    RaSubarray ty n m st => Some ra

    | _, _ => None
    end.

Fixpoint update_record (f : record_abs -> option record_abs) dba (rn : record_name) :
        option database_abs :=
    match dba, rn with
    | [], _ => None
    | ra :: dba', 0 =>
            match f ra with
            | None => None
            | Some ra' => Some (ra' :: dba')
            end
    | ra :: dba', S rn' =>
            match update_record f dba' rn' with
            | None => None
            | Some dba'' => Some (ra :: dba'')
            end
    end.

Definition write_record_field dba rn fn val :=
    update_record (fun ra => write_field ra fn val) dba rn.

Definition read_record_field dba rn fn :=
    lookup dba rn >>= fun ra =>
    read_field ra fn.

Tactic Notation "destruct_record_abs" constr(r) "as" "[" ident(x) "]" :=
    destruct r as [
        x | x | x | (* acalcout*) ?n x | x |
        x | x | x | x | x |
        x | x | x | x | x |
        x | (* waveform *) ?ty ?n x | (* subArray *) ?ty ?n ?m x | x
    ].

Tactic Notation "destruct_record_abs" constr(r) := destruct_record_abs r as [a].

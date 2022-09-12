Require Import ZArith.
Require Import String.
Require Import Flocq.Appli.Fappli_IEEE_bits.

Require Import v1.NeutronTactics.
Require Import v1.Multi.
Require Import v1.FloatAux.

Require Import epics.SpecTypes.
Require epics.Opcodes.
Require epics.SpecDenote.
Require epics.SpecRecords.
Require epics.Records.
Require epics.Types.
Require epics.Termination.
Require epics.Wf.
Require floatabs.AbsInt.
Require floatabs.Generate.
Require floatabs.Records.
Require validate.Validate.

(* Make the extracted code a little nicer. *)
Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellNatNum.
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellZNum.


Definition typecheck_database dbp :=
    let dbt := epics.Opcodes.database_program_type dbp in
    epics.Wf.check_wfm_database dbt dbp.


(* fix references through a module alias *)
Extract Inductive floatabs.Generate.Abs.record_abs =>
    "Record_abs" [
        "RaCalc"
        "RaCalcOut"
        "RaStrCalcOut"
        "RaArrayCalcOut"
        "RaFanout"
        "RaAnalogIn"
        "RaAnalogOut"
        "RaBinaryIn"
        "RaBinaryOut"
        "RaMBBO"
        "RaStringIn"
        "RaStringOut"
        "RaLongIn"
        "RaLongOut"
        "RaDFanout"
        "RaSeq"
        "RaWaveform"
        "RaSubarray"
        "RaAsyn"
    ].

Extract Inductive floatabs.AbsInt.Abs.calc_abs =>
    "Calc_abs" [
        "CalcAbs"
    ].

Extract Inductive floatabs.AbsInt.Abs.calc_out_abs =>
    "Calc_out_abs" [
        "CalcOutAbs"
    ].


Extract Inlined Constant Peano_dec.eq_nat_dec =>
    "((Prelude.==) :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool)".

Extraction Language Haskell.
Extraction "Query2.hs"
    epics.SpecRecords.record
    epics.SpecRecords.record_config
    epics.SpecRecords.record_state
    epics.SpecOpcodes.record_program

    epics.SpecRecords.database
    epics.SpecRecords.database_config
    epics.SpecRecords.database_state
    epics.SpecOpcodes.database_program

    epics.SpecDenote.compile_database
    typecheck_database

    (* floatabs *)
    floatabs.Generate.float_abs_init
    floatabs.Generate.float_abs_update
    floatabs.Generate.float_abs_truncate
    floatabs.Generate.float_abs_apply_overrides
    floatabs.AbsInt.float_abs_check
    floatabs.Records.float_abs_read_field   (* used for printing *)
    floatabs.Records.record_abs_type

    (* termination / cycle check *)
    epics.Termination.check_database_time
    epics.Termination.check_database_time_with_fuel

    (* trace validator *)
    validate.Validate.validate_trace
    validate.Validate.validate_trace_multi_record
    validate.Validate.validate_trace_event_loop

    (* utility functions *)
    b64_opp b64_plus b64_minus b64_mult b64_div b64_sqrt
    b64_of_bits bits_of_b64
    LONG_MAX
    default_array
    epics.Records.default_record

    (*
    (* types *)
    value in_link out_link fwd_link

    (* functions *)
    init_state run_state enqueue_event
    field_read field_write
    multi_rep multi_get multi_set
    default_array
    LONG_MAX

    compile_dbp
    FloatAbsInt.float_abs_init
    FloatAbsInt.float_abs_update
    FloatAbsInt.float_abs_check
    *)
    .


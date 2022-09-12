Require Import Arith.
Require Import ZArith.
Require Import List.
Import ListNotations.

Require Import v1.NeutronTactics.
Require Import v1.Util.
Require Import v1.Multi.
Require Import v1.Expr.

Require Import v1.EpicsTypes.

Require v1.EpicsRecordsBase.


Definition abs_value := option (Z * Z).


(* calc *)
Record calc_abs : Set :=
    CalcAbs {
        calc_A_to_L : multi 12 abs_value;
        calc_VAL : abs_value
    }.

(* calc_out *)
Record calc_out_abs : Set :=
    CalcOutAbs {
        calc_out_A_to_L : multi 12 abs_value;
        calc_out_VAL : abs_value;
        calc_out_PVAL : abs_value;
        calc_out_OVAL : abs_value;
        calc_out_tmp0 : abs_value
    }.

(* str_calc_out *)
Record str_calc_out_abs : Set :=
    StrCalcOutAbs {
        str_calc_out_A_to_L : multi 12 abs_value;
        (* str_calc_out_AA_to_LL : HAVOC; *)
        str_calc_out_VAL : abs_value;
        (* str_calc_out_SVAL : HAVOC; *)
        str_calc_out_PVAL : abs_value;
        str_calc_out_OVAL : abs_value;
        (* str_calc_out_OSV : HAVOC; *)
        str_calc_out_tmp0 : abs_value
    }.

(* array_calc_out *)
Record array_calc_out_abs {n : nat} : Set :=
    ArrayCalcOutAbs {
        array_calc_out_A_to_L : multi 12 abs_value;
        (* array_calc_out_AA_to_LL : HAVOC; *)
        array_calc_out_VAL : abs_value;
        (* array_calc_out_AVAL : HAVOC; *)
        array_calc_out_PVAL : abs_value;
        array_calc_out_OVAL : abs_value;
        (* array_calc_out_OAV : HAVOC; *)
        array_calc_out_tmp0 : abs_value
    }.
Implicit Arguments array_calc_out_abs.

(* fanout *)
Record fanout_abs : Set :=
    FanoutAbs {
    }.

(* ai *)
Record analog_in_abs : Set :=
    AnalogInAbs {
        analog_in_VAL : abs_value
    }.

(* ao *)
Record analog_out_abs : Set :=
    AnalogOutAbs {
        analog_out_VAL : abs_value;
        analog_out_PVAL : abs_value
    }.

(* bi *)
Record binary_in_abs : Set :=
    BinaryInAbs {
        binary_in_VAL : abs_value
    }.

(* bo *)
Record binary_out_abs : Set :=
    BinaryOutAbs {
        binary_out_VAL : abs_value;
    }.

(* mbbo *)
Record mbbo_abs : Set :=
    MBBOAbs {
        mbbo_VAL : abs_value
    }.

(* stringin *)
Record string_in_abs : Set :=
    StringInAbs {
    }.

(* stringout *)
Record string_out_abs : Set :=
    StringOutAbs {
    }.

(* longin *)
Record long_in_abs : Set :=
    LongInAbs {
        long_in_VAL : abs_value
    }.

(* longout *)
Record long_out_abs : Set :=
    LongOutAbs {
        long_out_VAL : abs_value
    }.

(* dfanout *)
Record dfanout_abs : Set :=
    DFanoutAbs {
        dfanout_VAL : abs_value
    }.

(* seq *)
Record seq_abs : Set :=
    SeqAbs {
        seq_DO1_to_DOA : multi 10 abs_value
    }.

(* waveform *)
Record waveform_abs {ty : elem_type} {n : nat} : Set :=
    WaveformAbs {
        (* waveform_VAL : HAVOC *)
    }.
Implicit Arguments waveform_abs.

(* subarray *)
Record subarray_abs {ty : elem_type} {n m : nat} : Set :=
    SubarrayAbs {
        (* subarray_VAL : HAVOC; *)
        (* subarray_tmp0 : HAVOC *)
    }.
Implicit Arguments subarray_abs.

(* asyn *)
Record asyn_abs : Set :=
    AsynAbs {
    }.

Definition set_calc_A_to_L  (r : calc_abs ) x0' : calc_abs  :=
    let '(CalcAbs  x0 x1) := r in
    CalcAbs  x0' x1.

Definition set_calc_VAL  (r : calc_abs ) x1' : calc_abs  :=
    let '(CalcAbs  x0 x1) := r in
    CalcAbs  x0 x1'.

Definition set_calc_out_A_to_L  (r : calc_out_abs ) x0' : calc_out_abs  :=
    let '(CalcOutAbs  x0 x1 x2 x3 x4) := r in
    CalcOutAbs  x0' x1 x2 x3 x4.

Definition set_calc_out_VAL  (r : calc_out_abs ) x1' : calc_out_abs  :=
    let '(CalcOutAbs  x0 x1 x2 x3 x4) := r in
    CalcOutAbs  x0 x1' x2 x3 x4.

Definition set_calc_out_PVAL  (r : calc_out_abs ) x2' : calc_out_abs  :=
    let '(CalcOutAbs  x0 x1 x2 x3 x4) := r in
    CalcOutAbs  x0 x1 x2' x3 x4.

Definition set_calc_out_OVAL  (r : calc_out_abs ) x3' : calc_out_abs  :=
    let '(CalcOutAbs  x0 x1 x2 x3 x4) := r in
    CalcOutAbs  x0 x1 x2 x3' x4.

Definition set_calc_out_tmp0  (r : calc_out_abs ) x4' : calc_out_abs  :=
    let '(CalcOutAbs  x0 x1 x2 x3 x4) := r in
    CalcOutAbs  x0 x1 x2 x3 x4'.

Definition set_str_calc_out_A_to_L  (r : str_calc_out_abs ) x0' : str_calc_out_abs  :=
    let '(StrCalcOutAbs  x0 x1 x2 x3 x4) := r in
    StrCalcOutAbs  x0' x1 x2 x3 x4.

Definition set_str_calc_out_VAL  (r : str_calc_out_abs ) x1' : str_calc_out_abs  :=
    let '(StrCalcOutAbs  x0 x1 x2 x3 x4) := r in
    StrCalcOutAbs  x0 x1' x2 x3 x4.

Definition set_str_calc_out_PVAL  (r : str_calc_out_abs ) x2' : str_calc_out_abs  :=
    let '(StrCalcOutAbs  x0 x1 x2 x3 x4) := r in
    StrCalcOutAbs  x0 x1 x2' x3 x4.

Definition set_str_calc_out_OVAL  (r : str_calc_out_abs ) x3' : str_calc_out_abs  :=
    let '(StrCalcOutAbs  x0 x1 x2 x3 x4) := r in
    StrCalcOutAbs  x0 x1 x2 x3' x4.

Definition set_str_calc_out_tmp0  (r : str_calc_out_abs ) x4' : str_calc_out_abs  :=
    let '(StrCalcOutAbs  x0 x1 x2 x3 x4) := r in
    StrCalcOutAbs  x0 x1 x2 x3 x4'.

Definition set_array_calc_out_A_to_L {n} (r : array_calc_out_abs n) x0' : array_calc_out_abs n :=
    let '(ArrayCalcOutAbs _ x0 x1 x2 x3 x4) := r in
    ArrayCalcOutAbs _ x0' x1 x2 x3 x4.

Definition set_array_calc_out_VAL {n} (r : array_calc_out_abs n) x1' : array_calc_out_abs n :=
    let '(ArrayCalcOutAbs _ x0 x1 x2 x3 x4) := r in
    ArrayCalcOutAbs _ x0 x1' x2 x3 x4.

Definition set_array_calc_out_PVAL {n} (r : array_calc_out_abs n) x2' : array_calc_out_abs n :=
    let '(ArrayCalcOutAbs _ x0 x1 x2 x3 x4) := r in
    ArrayCalcOutAbs _ x0 x1 x2' x3 x4.

Definition set_array_calc_out_OVAL {n} (r : array_calc_out_abs n) x3' : array_calc_out_abs n :=
    let '(ArrayCalcOutAbs _ x0 x1 x2 x3 x4) := r in
    ArrayCalcOutAbs _ x0 x1 x2 x3' x4.

Definition set_array_calc_out_tmp0 {n} (r : array_calc_out_abs n) x4' : array_calc_out_abs n :=
    let '(ArrayCalcOutAbs _ x0 x1 x2 x3 x4) := r in
    ArrayCalcOutAbs _ x0 x1 x2 x3 x4'.

Definition set_analog_in_VAL  (r : analog_in_abs ) x0' : analog_in_abs  :=
    let '(AnalogInAbs  x0) := r in
    AnalogInAbs  x0'.

Definition set_analog_out_VAL  (r : analog_out_abs ) x0' : analog_out_abs  :=
    let '(AnalogOutAbs  x0 x1) := r in
    AnalogOutAbs  x0' x1.

Definition set_analog_out_PVAL  (r : analog_out_abs ) x1' : analog_out_abs  :=
    let '(AnalogOutAbs  x0 x1) := r in
    AnalogOutAbs  x0 x1'.

Definition set_binary_in_VAL  (r : binary_in_abs ) x0' : binary_in_abs  :=
    let '(BinaryInAbs  x0) := r in
    BinaryInAbs  x0'.

Definition set_binary_out_VAL  (r : binary_out_abs ) x0' : binary_out_abs  :=
    let '(BinaryOutAbs  x0) := r in
    BinaryOutAbs  x0'.

Definition set_mbbo_VAL  (r : mbbo_abs ) x0' : mbbo_abs  :=
    let '(MBBOAbs  x0) := r in
    MBBOAbs  x0'.

Definition set_long_in_VAL  (r : long_in_abs ) x0' : long_in_abs  :=
    let '(LongInAbs  x0) := r in
    LongInAbs  x0'.

Definition set_long_out_VAL  (r : long_out_abs ) x0' : long_out_abs  :=
    let '(LongOutAbs  x0) := r in
    LongOutAbs  x0'.

Definition set_dfanout_VAL  (r : dfanout_abs ) x0' : dfanout_abs  :=
    let '(DFanoutAbs  x0) := r in
    DFanoutAbs  x0'.

Definition set_seq_DO1_to_DOA  (r : seq_abs ) x0' : seq_abs  :=
    let '(SeqAbs  x0) := r in
    SeqAbs  x0'.

Require Import v1.Multi.

Require Import epics.SpecTypes.
Require Import expr.Expr.


(* Common enums *)

Inductive output_mode :=
| Supervisory
| ClosedLoop.

Inductive output_exec : Set :=
| EveryTime : output_exec
| OnChange : output_exec
| WhenZero : output_exec
| WhenNonzero : output_exec
| TransitionToZero : output_exec
| TransitionToNonzero : output_exec.

Inductive output_data : Set :=
| UseCalc : output_data
| UseOcal : output_data.

Definition output_data_eq_dec (x y : output_data) : { x = y } + { x <> y }.
decide equality.
Defined.


(* calc *)

Record calc_state : Set :=
    CalcState {
        calc_A_to_L : multi 12 e_double;
        calc_VAL : e_double
    }.
Record calc_config : Set :=
    CalcConfig {
        calc_CALC : expr e_double 12;
        calc_INPA_to_INPL : multi 12 in_link;
        calc_FLNK : fwd_link
    }.


(* calcout *)

Record calc_out_state : Set :=
    CalcOutState {
        calc_out_A_to_L : multi 12 e_double;
        calc_out_VAL : e_double;
        calc_out_PVAL : e_double;
        calc_out_OVAL : e_double;
        calc_out_tmp0 : e_double
    }.
Record calc_out_config : Set :=
    CalcOutConfig {
        calc_out_CALC : expr e_double 12;
        calc_out_OCAL : expr e_double 12;
        calc_out_INPA_to_INPL : multi 12 in_link;
        calc_out_OUT : out_link;
        calc_out_FLNK : fwd_link;
        calc_out_OOPT : output_exec;
        calc_out_DOPT : output_data
    }.


(* scalcout *)

Record str_calc_out_state : Set :=
    StrCalcOutState {
        str_calc_out_A_to_L : multi 12 e_double;
        str_calc_out_AA_to_LL : multi 12 e_string;
        str_calc_out_VAL : e_double;
        str_calc_out_SVAL : e_string;
        str_calc_out_PVAL : e_double;
        str_calc_out_OVAL : e_double;
        str_calc_out_OSV : e_string;
        str_calc_out_tmp0 : e_double
    }.
Record str_calc_out_config : Set :=
    StrCalcOutConfig {
        str_calc_out_CALC : expr (e_double + e_string) 12;
        str_calc_out_OCAL : expr (e_double + e_string) 12;
        str_calc_out_INPA_to_INPL : multi 12 in_link;
        str_calc_out_INAA_to_INLL : multi 12 in_link;
        str_calc_out_OUT : out_link;
        str_calc_out_FLNK : fwd_link;
        str_calc_out_OOPT : output_exec;
        str_calc_out_DOPT : output_data
    }.


(* acalcout *)

(* Similar to "waveform", we have a family of "acalcout" record types. *)
(* Declare `n` to be implicit, so it will be implicit in the accessor
   functions.  We make it non-implicit for the actual type just below. *)
Record array_calc_out_state {n : nat} : Set :=
    ArrayCalcOutState {
        array_calc_out_A_to_L : multi 12 e_double;
        array_calc_out_AA_to_LL : multi 12 (e_array TeDouble n);
        array_calc_out_VAL : e_double;
        array_calc_out_AVAL : e_array TeDouble n;
        array_calc_out_PVAL : e_double;
        array_calc_out_OVAL : e_double;
        array_calc_out_OAV : e_array TeDouble n;
        array_calc_out_tmp0 : e_double
    }.
Record array_calc_out_config {n : nat} : Set :=
    ArrayCalcOutConfig {
        array_calc_out_CALC : expr (e_double + e_array TeDouble n) 12;
        array_calc_out_OCAL : expr (e_double + e_array TeDouble n) 12;
        array_calc_out_INPA_to_INPL : multi 12 in_link;
        array_calc_out_INAA_to_INLL : multi 12 in_link;
        array_calc_out_OUT : out_link;
        array_calc_out_FLNK : fwd_link;
        array_calc_out_OOPT : output_exec;
        array_calc_out_DOPT : output_data
    }.
Implicit Arguments array_calc_out_state.
Implicit Arguments array_calc_out_config.


(* fanout *)

Record fanout_state : Set :=
    FanoutState {
    }.
Record fanout_config : Set :=
    FanoutConfig {
        fanout_LNK1_to_LNK6 : multi 6 fwd_link
    }.


(* ai *)

Record analog_in_state : Set :=
    AnalogInState {
        analog_in_VAL : e_double
    }.
Record analog_in_config : Set :=
    AnalogInConfig {
        analog_in_FLNK : fwd_link
    }.


(* ao *)

Record analog_out_state : Set :=
    AnalogOutState {
        analog_out_VAL : e_double;
        analog_out_PVAL : e_double
    }.
Record analog_out_config : Set :=
    AnalogOutConfig {
        analog_out_DOL : in_link;
        analog_out_FLNK : fwd_link
    }.


(* bi *)

Record binary_in_state : Set :=
    BinaryInState {
        binary_in_VAL : e_enum
    }.
Record binary_in_config : Set :=
    BinaryInConfig {
        binary_in_FLNK : fwd_link
    }.


(* bo *)

Record binary_out_state : Set :=
    BinaryOutState {
        binary_out_VAL : e_enum
    }.
Record binary_out_config : Set :=
    BinaryOutConfig {
        binary_out_DOL : in_link;
        binary_out_FLNK : fwd_link
    }.


(* mbbo *)

Record mbbo_state : Set :=
    MBBOState {
        mbbo_VAL : e_enum
    }.
Record mbbo_config : Set :=
    MBBOConfig {
        mbbo_DOL : in_link;
        mbbo_FLNK : fwd_link
    }.


(* stringin *)

Record string_in_state : Set :=
    StringInState {
        string_in_VAL : e_string
    }.
Record string_in_config : Set :=
    StringInConfig {
        string_in_FLNK : fwd_link
    }.


(* stringout *)

Record string_out_state : Set :=
    StringOutState {
        string_out_VAL : e_string
    }.
Record string_out_config : Set :=
    StringOutConfig {
        string_out_DOL : in_link;
        string_out_FLNK : fwd_link
    }.


(* longin *)

Record long_in_state : Set :=
    LongInState {
        long_in_VAL : e_long
    }.
Record long_in_config : Set :=
    LongInConfig {
        long_in_FLNK : fwd_link
    }.


(* longout *)

Record long_out_state : Set :=
    LongOutState {
        long_out_VAL : e_long
    }.
Record long_out_config : Set :=
    LongOutConfig {
        long_out_DOL : in_link;
        long_out_FLNK : fwd_link
    }.


(* dfanout *)

Record dfanout_state : Set :=
    DFanoutState {
        dfanout_VAL : e_double
    }.
Record dfanout_config : Set :=
    DFanoutConfig {
        dfanout_DOL : in_link;
        dfanout_OUTA_to_OUTH : multi 8 out_link;
        (* TODO: OMSL *)
        dfanout_FLNK : fwd_link
    }.


(* seq *)

Record seq_state : Set :=
    SeqState {
        seq_DO1_to_DOA : multi 10 e_double;
        seq_PACT : e_enum
    }.
Record seq_config : Set :=
    SeqConfig {
        seq_DOL1_to_DOLA : multi 10 in_link;
        seq_LNK1_to_LNKA : multi 10 out_link
    }.


(* waveform *)

(* Think of it this way: EPICS doesn't have just a single "waveform" record
   type, it actually has a whole family of record types, indexed by their FTVL
   and NELM fields. *)

Record waveform_state {ty : elem_type} {n : nat} : Set :=
    WaveformState {
        waveform_VAL : e_array ty n
    }.
Record waveform_config {ty : elem_type} {n : nat} : Set :=
    WaveformConfig {
        waveform_INP : in_link;
        waveform_FLNK : fwd_link
    }.
Implicit Arguments waveform_state.
Implicit Arguments waveform_config.

(* Accessors for config fields that appear as parameters *)
Definition waveform_FTVL {ty} {n} (r : waveform_config ty n) := ty.
Definition waveform_NELM {ty} {n} (r : waveform_config ty n) := n.


(* subArray *)

Record subarray_state {ty : elem_type} {n m : nat} : Set :=
    SubarrayState {
        (* VAL holds the result, an array of length NELM.
           tmp0 holds the input value, an array of length MALM > NELM. *)
        subarray_VAL : e_array ty n;
        subarray_tmp0 : e_array ty m
    }.
Record subarray_config {ty : elem_type} {n m : nat} : Set :=
    SubarrayConfig {
        subarray_INP : in_link;
        subarray_INDX : nat;
        subarray_FLNK : fwd_link
    }.
Implicit Arguments subarray_state.
Implicit Arguments subarray_config.

(* Accessors for config fields that appear as parameters *)
Definition subarray_FTVL {ty} {n m} (r : subarray_config ty n m) := ty.
Definition subarray_NELM {ty} {n m} (r : subarray_config ty n m) := n.
Definition subarray_MALM {ty} {n m} (r : subarray_config ty n m) := m.


(* asyn *)

Record asyn_state : Set :=
    AsynState {
    }.
Record asyn_config : Set :=
    AsynConfig {
    }.

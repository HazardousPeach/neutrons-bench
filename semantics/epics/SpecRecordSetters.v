Require Import epics.SpecRecordData.

Definition set_calc_A_to_L  (r : calc_state ) x0' : calc_state  :=
    let '(CalcState  x0 x1) := r in
    CalcState  x0' x1.

Definition set_calc_VAL  (r : calc_state ) x1' : calc_state  :=
    let '(CalcState  x0 x1) := r in
    CalcState  x0 x1'.

Definition set_calc_CALC  (r : calc_config ) x0' : calc_config  :=
    let '(CalcConfig  x0 x1 x2) := r in
    CalcConfig  x0' x1 x2.

Definition set_calc_INPA_to_INPL  (r : calc_config ) x1' : calc_config  :=
    let '(CalcConfig  x0 x1 x2) := r in
    CalcConfig  x0 x1' x2.

Definition set_calc_FLNK  (r : calc_config ) x2' : calc_config  :=
    let '(CalcConfig  x0 x1 x2) := r in
    CalcConfig  x0 x1 x2'.

Definition set_calc_out_A_to_L  (r : calc_out_state ) x0' : calc_out_state  :=
    let '(CalcOutState  x0 x1 x2 x3 x4) := r in
    CalcOutState  x0' x1 x2 x3 x4.

Definition set_calc_out_VAL  (r : calc_out_state ) x1' : calc_out_state  :=
    let '(CalcOutState  x0 x1 x2 x3 x4) := r in
    CalcOutState  x0 x1' x2 x3 x4.

Definition set_calc_out_PVAL  (r : calc_out_state ) x2' : calc_out_state  :=
    let '(CalcOutState  x0 x1 x2 x3 x4) := r in
    CalcOutState  x0 x1 x2' x3 x4.

Definition set_calc_out_OVAL  (r : calc_out_state ) x3' : calc_out_state  :=
    let '(CalcOutState  x0 x1 x2 x3 x4) := r in
    CalcOutState  x0 x1 x2 x3' x4.

Definition set_calc_out_tmp0  (r : calc_out_state ) x4' : calc_out_state  :=
    let '(CalcOutState  x0 x1 x2 x3 x4) := r in
    CalcOutState  x0 x1 x2 x3 x4'.

Definition set_calc_out_CALC  (r : calc_out_config ) x0' : calc_out_config  :=
    let '(CalcOutConfig  x0 x1 x2 x3 x4 x5 x6) := r in
    CalcOutConfig  x0' x1 x2 x3 x4 x5 x6.

Definition set_calc_out_OCAL  (r : calc_out_config ) x1' : calc_out_config  :=
    let '(CalcOutConfig  x0 x1 x2 x3 x4 x5 x6) := r in
    CalcOutConfig  x0 x1' x2 x3 x4 x5 x6.

Definition set_calc_out_INPA_to_INPL  (r : calc_out_config ) x2' : calc_out_config  :=
    let '(CalcOutConfig  x0 x1 x2 x3 x4 x5 x6) := r in
    CalcOutConfig  x0 x1 x2' x3 x4 x5 x6.

Definition set_calc_out_OUT  (r : calc_out_config ) x3' : calc_out_config  :=
    let '(CalcOutConfig  x0 x1 x2 x3 x4 x5 x6) := r in
    CalcOutConfig  x0 x1 x2 x3' x4 x5 x6.

Definition set_calc_out_FLNK  (r : calc_out_config ) x4' : calc_out_config  :=
    let '(CalcOutConfig  x0 x1 x2 x3 x4 x5 x6) := r in
    CalcOutConfig  x0 x1 x2 x3 x4' x5 x6.

Definition set_calc_out_OOPT  (r : calc_out_config ) x5' : calc_out_config  :=
    let '(CalcOutConfig  x0 x1 x2 x3 x4 x5 x6) := r in
    CalcOutConfig  x0 x1 x2 x3 x4 x5' x6.

Definition set_calc_out_DOPT  (r : calc_out_config ) x6' : calc_out_config  :=
    let '(CalcOutConfig  x0 x1 x2 x3 x4 x5 x6) := r in
    CalcOutConfig  x0 x1 x2 x3 x4 x5 x6'.

Definition set_str_calc_out_A_to_L  (r : str_calc_out_state ) x0' : str_calc_out_state  :=
    let '(StrCalcOutState  x0 x1 x2 x3 x4 x5 x6 x7) := r in
    StrCalcOutState  x0' x1 x2 x3 x4 x5 x6 x7.

Definition set_str_calc_out_AA_to_LL  (r : str_calc_out_state ) x1' : str_calc_out_state  :=
    let '(StrCalcOutState  x0 x1 x2 x3 x4 x5 x6 x7) := r in
    StrCalcOutState  x0 x1' x2 x3 x4 x5 x6 x7.

Definition set_str_calc_out_VAL  (r : str_calc_out_state ) x2' : str_calc_out_state  :=
    let '(StrCalcOutState  x0 x1 x2 x3 x4 x5 x6 x7) := r in
    StrCalcOutState  x0 x1 x2' x3 x4 x5 x6 x7.

Definition set_str_calc_out_SVAL  (r : str_calc_out_state ) x3' : str_calc_out_state  :=
    let '(StrCalcOutState  x0 x1 x2 x3 x4 x5 x6 x7) := r in
    StrCalcOutState  x0 x1 x2 x3' x4 x5 x6 x7.

Definition set_str_calc_out_PVAL  (r : str_calc_out_state ) x4' : str_calc_out_state  :=
    let '(StrCalcOutState  x0 x1 x2 x3 x4 x5 x6 x7) := r in
    StrCalcOutState  x0 x1 x2 x3 x4' x5 x6 x7.

Definition set_str_calc_out_OVAL  (r : str_calc_out_state ) x5' : str_calc_out_state  :=
    let '(StrCalcOutState  x0 x1 x2 x3 x4 x5 x6 x7) := r in
    StrCalcOutState  x0 x1 x2 x3 x4 x5' x6 x7.

Definition set_str_calc_out_OSV  (r : str_calc_out_state ) x6' : str_calc_out_state  :=
    let '(StrCalcOutState  x0 x1 x2 x3 x4 x5 x6 x7) := r in
    StrCalcOutState  x0 x1 x2 x3 x4 x5 x6' x7.

Definition set_str_calc_out_tmp0  (r : str_calc_out_state ) x7' : str_calc_out_state  :=
    let '(StrCalcOutState  x0 x1 x2 x3 x4 x5 x6 x7) := r in
    StrCalcOutState  x0 x1 x2 x3 x4 x5 x6 x7'.

Definition set_str_calc_out_CALC  (r : str_calc_out_config ) x0' : str_calc_out_config  :=
    let '(StrCalcOutConfig  x0 x1 x2 x3 x4 x5 x6 x7) := r in
    StrCalcOutConfig  x0' x1 x2 x3 x4 x5 x6 x7.

Definition set_str_calc_out_OCAL  (r : str_calc_out_config ) x1' : str_calc_out_config  :=
    let '(StrCalcOutConfig  x0 x1 x2 x3 x4 x5 x6 x7) := r in
    StrCalcOutConfig  x0 x1' x2 x3 x4 x5 x6 x7.

Definition set_str_calc_out_INPA_to_INPL  (r : str_calc_out_config ) x2' : str_calc_out_config  :=
    let '(StrCalcOutConfig  x0 x1 x2 x3 x4 x5 x6 x7) := r in
    StrCalcOutConfig  x0 x1 x2' x3 x4 x5 x6 x7.

Definition set_str_calc_out_INAA_to_INLL  (r : str_calc_out_config ) x3' : str_calc_out_config  :=
    let '(StrCalcOutConfig  x0 x1 x2 x3 x4 x5 x6 x7) := r in
    StrCalcOutConfig  x0 x1 x2 x3' x4 x5 x6 x7.

Definition set_str_calc_out_OUT  (r : str_calc_out_config ) x4' : str_calc_out_config  :=
    let '(StrCalcOutConfig  x0 x1 x2 x3 x4 x5 x6 x7) := r in
    StrCalcOutConfig  x0 x1 x2 x3 x4' x5 x6 x7.

Definition set_str_calc_out_FLNK  (r : str_calc_out_config ) x5' : str_calc_out_config  :=
    let '(StrCalcOutConfig  x0 x1 x2 x3 x4 x5 x6 x7) := r in
    StrCalcOutConfig  x0 x1 x2 x3 x4 x5' x6 x7.

Definition set_str_calc_out_OOPT  (r : str_calc_out_config ) x6' : str_calc_out_config  :=
    let '(StrCalcOutConfig  x0 x1 x2 x3 x4 x5 x6 x7) := r in
    StrCalcOutConfig  x0 x1 x2 x3 x4 x5 x6' x7.

Definition set_str_calc_out_DOPT  (r : str_calc_out_config ) x7' : str_calc_out_config  :=
    let '(StrCalcOutConfig  x0 x1 x2 x3 x4 x5 x6 x7) := r in
    StrCalcOutConfig  x0 x1 x2 x3 x4 x5 x6 x7'.

Definition set_array_calc_out_A_to_L {n} (r : array_calc_out_state n) x0' : array_calc_out_state n :=
    let '(ArrayCalcOutState _ x0 x1 x2 x3 x4 x5 x6 x7) := r in
    ArrayCalcOutState _ x0' x1 x2 x3 x4 x5 x6 x7.

Definition set_array_calc_out_AA_to_LL {n} (r : array_calc_out_state n) x1' : array_calc_out_state n :=
    let '(ArrayCalcOutState _ x0 x1 x2 x3 x4 x5 x6 x7) := r in
    ArrayCalcOutState _ x0 x1' x2 x3 x4 x5 x6 x7.

Definition set_array_calc_out_VAL {n} (r : array_calc_out_state n) x2' : array_calc_out_state n :=
    let '(ArrayCalcOutState _ x0 x1 x2 x3 x4 x5 x6 x7) := r in
    ArrayCalcOutState _ x0 x1 x2' x3 x4 x5 x6 x7.

Definition set_array_calc_out_AVAL {n} (r : array_calc_out_state n) x3' : array_calc_out_state n :=
    let '(ArrayCalcOutState _ x0 x1 x2 x3 x4 x5 x6 x7) := r in
    ArrayCalcOutState _ x0 x1 x2 x3' x4 x5 x6 x7.

Definition set_array_calc_out_PVAL {n} (r : array_calc_out_state n) x4' : array_calc_out_state n :=
    let '(ArrayCalcOutState _ x0 x1 x2 x3 x4 x5 x6 x7) := r in
    ArrayCalcOutState _ x0 x1 x2 x3 x4' x5 x6 x7.

Definition set_array_calc_out_OVAL {n} (r : array_calc_out_state n) x5' : array_calc_out_state n :=
    let '(ArrayCalcOutState _ x0 x1 x2 x3 x4 x5 x6 x7) := r in
    ArrayCalcOutState _ x0 x1 x2 x3 x4 x5' x6 x7.

Definition set_array_calc_out_OAV {n} (r : array_calc_out_state n) x6' : array_calc_out_state n :=
    let '(ArrayCalcOutState _ x0 x1 x2 x3 x4 x5 x6 x7) := r in
    ArrayCalcOutState _ x0 x1 x2 x3 x4 x5 x6' x7.

Definition set_array_calc_out_tmp0 {n} (r : array_calc_out_state n) x7' : array_calc_out_state n :=
    let '(ArrayCalcOutState _ x0 x1 x2 x3 x4 x5 x6 x7) := r in
    ArrayCalcOutState _ x0 x1 x2 x3 x4 x5 x6 x7'.

Definition set_array_calc_out_CALC {n} (r : array_calc_out_config n) x0' : array_calc_out_config n :=
    let '(ArrayCalcOutConfig _ x0 x1 x2 x3 x4 x5 x6 x7) := r in
    ArrayCalcOutConfig _ x0' x1 x2 x3 x4 x5 x6 x7.

Definition set_array_calc_out_OCAL {n} (r : array_calc_out_config n) x1' : array_calc_out_config n :=
    let '(ArrayCalcOutConfig _ x0 x1 x2 x3 x4 x5 x6 x7) := r in
    ArrayCalcOutConfig _ x0 x1' x2 x3 x4 x5 x6 x7.

Definition set_array_calc_out_INPA_to_INPL {n} (r : array_calc_out_config n) x2' : array_calc_out_config n :=
    let '(ArrayCalcOutConfig _ x0 x1 x2 x3 x4 x5 x6 x7) := r in
    ArrayCalcOutConfig _ x0 x1 x2' x3 x4 x5 x6 x7.

Definition set_array_calc_out_INAA_to_INLL {n} (r : array_calc_out_config n) x3' : array_calc_out_config n :=
    let '(ArrayCalcOutConfig _ x0 x1 x2 x3 x4 x5 x6 x7) := r in
    ArrayCalcOutConfig _ x0 x1 x2 x3' x4 x5 x6 x7.

Definition set_array_calc_out_OUT {n} (r : array_calc_out_config n) x4' : array_calc_out_config n :=
    let '(ArrayCalcOutConfig _ x0 x1 x2 x3 x4 x5 x6 x7) := r in
    ArrayCalcOutConfig _ x0 x1 x2 x3 x4' x5 x6 x7.

Definition set_array_calc_out_FLNK {n} (r : array_calc_out_config n) x5' : array_calc_out_config n :=
    let '(ArrayCalcOutConfig _ x0 x1 x2 x3 x4 x5 x6 x7) := r in
    ArrayCalcOutConfig _ x0 x1 x2 x3 x4 x5' x6 x7.

Definition set_array_calc_out_OOPT {n} (r : array_calc_out_config n) x6' : array_calc_out_config n :=
    let '(ArrayCalcOutConfig _ x0 x1 x2 x3 x4 x5 x6 x7) := r in
    ArrayCalcOutConfig _ x0 x1 x2 x3 x4 x5 x6' x7.

Definition set_array_calc_out_DOPT {n} (r : array_calc_out_config n) x7' : array_calc_out_config n :=
    let '(ArrayCalcOutConfig _ x0 x1 x2 x3 x4 x5 x6 x7) := r in
    ArrayCalcOutConfig _ x0 x1 x2 x3 x4 x5 x6 x7'.

Definition set_fanout_LNK1_to_LNK6  (r : fanout_config ) x0' : fanout_config  :=
    let '(FanoutConfig  x0) := r in
    FanoutConfig  x0'.

Definition set_analog_in_VAL  (r : analog_in_state ) x0' : analog_in_state  :=
    let '(AnalogInState  x0) := r in
    AnalogInState  x0'.

Definition set_analog_in_FLNK  (r : analog_in_config ) x0' : analog_in_config  :=
    let '(AnalogInConfig  x0) := r in
    AnalogInConfig  x0'.

Definition set_analog_out_VAL  (r : analog_out_state ) x0' : analog_out_state  :=
    let '(AnalogOutState  x0 x1) := r in
    AnalogOutState  x0' x1.

Definition set_analog_out_PVAL  (r : analog_out_state ) x1' : analog_out_state  :=
    let '(AnalogOutState  x0 x1) := r in
    AnalogOutState  x0 x1'.

Definition set_analog_out_DOL  (r : analog_out_config ) x0' : analog_out_config  :=
    let '(AnalogOutConfig  x0 x1) := r in
    AnalogOutConfig  x0' x1.

Definition set_analog_out_FLNK  (r : analog_out_config ) x1' : analog_out_config  :=
    let '(AnalogOutConfig  x0 x1) := r in
    AnalogOutConfig  x0 x1'.

Definition set_binary_in_VAL  (r : binary_in_state ) x0' : binary_in_state  :=
    let '(BinaryInState  x0) := r in
    BinaryInState  x0'.

Definition set_binary_in_FLNK  (r : binary_in_config ) x0' : binary_in_config  :=
    let '(BinaryInConfig  x0) := r in
    BinaryInConfig  x0'.

Definition set_binary_out_VAL  (r : binary_out_state ) x0' : binary_out_state  :=
    let '(BinaryOutState  x0) := r in
    BinaryOutState  x0'.

Definition set_binary_out_DOL  (r : binary_out_config ) x0' : binary_out_config  :=
    let '(BinaryOutConfig  x0 x1) := r in
    BinaryOutConfig  x0' x1.

Definition set_binary_out_FLNK  (r : binary_out_config ) x1' : binary_out_config  :=
    let '(BinaryOutConfig  x0 x1) := r in
    BinaryOutConfig  x0 x1'.

Definition set_mbbo_VAL  (r : mbbo_state ) x0' : mbbo_state  :=
    let '(MBBOState  x0) := r in
    MBBOState  x0'.

Definition set_mbbo_DOL  (r : mbbo_config ) x0' : mbbo_config  :=
    let '(MBBOConfig  x0 x1) := r in
    MBBOConfig  x0' x1.

Definition set_mbbo_FLNK  (r : mbbo_config ) x1' : mbbo_config  :=
    let '(MBBOConfig  x0 x1) := r in
    MBBOConfig  x0 x1'.

Definition set_string_in_VAL  (r : string_in_state ) x0' : string_in_state  :=
    let '(StringInState  x0) := r in
    StringInState  x0'.

Definition set_string_in_FLNK  (r : string_in_config ) x0' : string_in_config  :=
    let '(StringInConfig  x0) := r in
    StringInConfig  x0'.

Definition set_string_out_VAL  (r : string_out_state ) x0' : string_out_state  :=
    let '(StringOutState  x0) := r in
    StringOutState  x0'.

Definition set_string_out_DOL  (r : string_out_config ) x0' : string_out_config  :=
    let '(StringOutConfig  x0 x1) := r in
    StringOutConfig  x0' x1.

Definition set_string_out_FLNK  (r : string_out_config ) x1' : string_out_config  :=
    let '(StringOutConfig  x0 x1) := r in
    StringOutConfig  x0 x1'.

Definition set_long_in_VAL  (r : long_in_state ) x0' : long_in_state  :=
    let '(LongInState  x0) := r in
    LongInState  x0'.

Definition set_long_in_FLNK  (r : long_in_config ) x0' : long_in_config  :=
    let '(LongInConfig  x0) := r in
    LongInConfig  x0'.

Definition set_long_out_VAL  (r : long_out_state ) x0' : long_out_state  :=
    let '(LongOutState  x0) := r in
    LongOutState  x0'.

Definition set_long_out_DOL  (r : long_out_config ) x0' : long_out_config  :=
    let '(LongOutConfig  x0 x1) := r in
    LongOutConfig  x0' x1.

Definition set_long_out_FLNK  (r : long_out_config ) x1' : long_out_config  :=
    let '(LongOutConfig  x0 x1) := r in
    LongOutConfig  x0 x1'.

Definition set_dfanout_VAL  (r : dfanout_state ) x0' : dfanout_state  :=
    let '(DFanoutState  x0) := r in
    DFanoutState  x0'.

Definition set_dfanout_DOL  (r : dfanout_config ) x0' : dfanout_config  :=
    let '(DFanoutConfig  x0 x1 x2) := r in
    DFanoutConfig  x0' x1 x2.

Definition set_dfanout_OUTA_to_OUTH  (r : dfanout_config ) x1' : dfanout_config  :=
    let '(DFanoutConfig  x0 x1 x2) := r in
    DFanoutConfig  x0 x1' x2.

Definition set_dfanout_FLNK  (r : dfanout_config ) x2' : dfanout_config  :=
    let '(DFanoutConfig  x0 x1 x2) := r in
    DFanoutConfig  x0 x1 x2'.

Definition set_seq_DO1_to_DOA  (r : seq_state ) x0' : seq_state  :=
    let '(SeqState  x0 x1) := r in
    SeqState  x0' x1.

Definition set_seq_PACT  (r : seq_state ) x1' : seq_state  :=
    let '(SeqState  x0 x1) := r in
    SeqState  x0 x1'.

Definition set_seq_DOL1_to_DOLA  (r : seq_config ) x0' : seq_config  :=
    let '(SeqConfig  x0 x1) := r in
    SeqConfig  x0' x1.

Definition set_seq_LNK1_to_LNKA  (r : seq_config ) x1' : seq_config  :=
    let '(SeqConfig  x0 x1) := r in
    SeqConfig  x0 x1'.

Definition set_waveform_VAL {ty} {n} (r : waveform_state ty n) x0' : waveform_state ty n :=
    let '(WaveformState _ _ x0) := r in
    WaveformState _ _ x0'.

Definition set_waveform_INP {ty} {n} (r : waveform_config ty n) x0' : waveform_config ty n :=
    let '(WaveformConfig _ _ x0 x1) := r in
    WaveformConfig _ _ x0' x1.

Definition set_waveform_FLNK {ty} {n} (r : waveform_config ty n) x1' : waveform_config ty n :=
    let '(WaveformConfig _ _ x0 x1) := r in
    WaveformConfig _ _ x0 x1'.

Definition set_subarray_VAL {ty} {n} {m} (r : subarray_state ty n m) x0' : subarray_state ty n m :=
    let '(SubarrayState _ _ _ x0 x1) := r in
    SubarrayState _ _ _ x0' x1.

Definition set_subarray_tmp0 {ty} {n} {m} (r : subarray_state ty n m) x1' : subarray_state ty n m :=
    let '(SubarrayState _ _ _ x0 x1) := r in
    SubarrayState _ _ _ x0 x1'.

Definition set_subarray_INP {ty} {n} {m} (r : subarray_config ty n m) x0' : subarray_config ty n m :=
    let '(SubarrayConfig _ _ _ x0 x1 x2) := r in
    SubarrayConfig _ _ _ x0' x1 x2.

Definition set_subarray_INDX {ty} {n} {m} (r : subarray_config ty n m) x1' : subarray_config ty n m :=
    let '(SubarrayConfig _ _ _ x0 x1 x2) := r in
    SubarrayConfig _ _ _ x0 x1' x2.

Definition set_subarray_FLNK {ty} {n} {m} (r : subarray_config ty n m) x2' : subarray_config ty n m :=
    let '(SubarrayConfig _ _ _ x0 x1 x2) := r in
    SubarrayConfig _ _ _ x0 x1 x2'.

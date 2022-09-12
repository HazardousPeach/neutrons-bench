Require Import floatabs.RecordData.

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

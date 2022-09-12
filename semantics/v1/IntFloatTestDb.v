Require Import List.
Import ListNotations.
Require Import ZArith.
Require Import v1.Epics.
Require Import v1.EpicsAux.
Require Import v1.Expr.
Require Import v1.Multi.
Require Import v1.FloatAux.

Definition idx0 : index 12 := $(mk_index 0)$.
Definition f_A : field_name := f_A_to_L idx0.
Definition EVarA : expr e_double 12 := EVar idx0.
Definition idx1 : index 12 := $(mk_index 1)$.
Definition f_B : field_name := f_A_to_L idx1.
Definition EVarB : expr e_double 12 := EVar idx1.
Definition idx2 : index 12 := $(mk_index 2)$.
Definition f_C : field_name := f_A_to_L idx2.
Definition EVarC : expr e_double 12 := EVar idx2.
Definition idx3 : index 12 := $(mk_index 3)$.
Definition f_D : field_name := f_A_to_L idx3.
Definition EVarD : expr e_double 12 := EVar idx3.
Definition idx4 : index 12 := $(mk_index 4)$.
Definition f_E : field_name := f_A_to_L idx4.
Definition EVarE : expr e_double 12 := EVar idx4.
Definition idx5 : index 12 := $(mk_index 5)$.
Definition f_F : field_name := f_A_to_L idx5.
Definition EVarF : expr e_double 12 := EVar idx5.
Definition idx6 : index 12 := $(mk_index 6)$.
Definition f_G : field_name := f_A_to_L idx6.
Definition EVarG : expr e_double 12 := EVar idx6.
Definition idx7 : index 12 := $(mk_index 7)$.
Definition f_H : field_name := f_A_to_L idx7.
Definition EVarH : expr e_double 12 := EVar idx7.
Definition idx8 : index 12 := $(mk_index 8)$.
Definition f_I : field_name := f_A_to_L idx8.
Definition EVarI : expr e_double 12 := EVar idx8.
Definition idx9 : index 12 := $(mk_index 9)$.
Definition f_J : field_name := f_A_to_L idx9.
Definition EVarJ : expr e_double 12 := EVar idx9.
Definition idx10 : index 12 := $(mk_index 10)$.
Definition f_K : field_name := f_A_to_L idx10.
Definition EVarK : expr e_double 12 := EVar idx10.
Definition idx11 : index 12 := $(mk_index 11)$.
Definition f_L : field_name := f_A_to_L idx11.
Definition EVarL : expr e_double 12 := EVar idx11.

Definition REC_in1 : record_name := 0.
Definition REC_calc1 : record_name := 1.
Definition REC_in2 : record_name := 2.
Definition REC_calc2 : record_name := 3.
Definition REC_combine : record_name := 4.

Definition my_dbc : database_config := [
    RcAnalogIn {|
        analog_in_FLNK := Some {| fl_rn := REC_calc1 |}
    |};
    RcCalc {|
        calc_INPA_to_INPL := (Some {| il_rn := REC_in1; il_fn := f_VAL; il_pp := NPP |},
                              None,
                              None,
                              None,
                              None,
                              None,
                              None,
                              None,
                              None,
                              None,
                              None,
                              None);
        calc_FLNK := Some {| fl_rn := REC_combine |};
        calc_CALC := denote_expr_double (EBinaryOp BLt (EVarA) (EConst (Z2B64 0)))
    |};
    RcAnalogIn {|
        analog_in_FLNK := Some {| fl_rn := REC_calc2 |}
    |};
    RcCalc {|
        calc_INPA_to_INPL := (Some {| il_rn := REC_in2; il_fn := f_VAL; il_pp := NPP |},
                              None,
                              None,
                              None,
                              None,
                              None,
                              None,
                              None,
                              None,
                              None,
                              None,
                              None);
        calc_FLNK := Some {| fl_rn := REC_combine |};
        calc_CALC := denote_expr_double (EBinaryOp BLt (EVarA) (EConst (Z2B64 0)))
    |};
    RcCalc {|
        calc_INPA_to_INPL := (Some {| il_rn := REC_calc1; il_fn := f_VAL; il_pp := NPP |},
                              Some {| il_rn := REC_calc2; il_fn := f_VAL; il_pp := NPP |},
                              None,
                              None,
                              None,
                              None,
                              None,
                              None,
                              None,
                              None,
                              None,
                              None);
        calc_FLNK := None;
        calc_CALC := denote_expr_double (EBinaryOp BAdd (EVarA) (EVarB))
    |}
].

Definition my_dbs : database_state := [
    RsAnalogIn {|
        analog_in_VAL := Z2B64 0
    |};
    RsCalc {|
        calc_A_to_L := (Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0);
        calc_VAL := Z2B64 0
    |};
    RsAnalogIn {|
        analog_in_VAL := Z2B64 0
    |};
    RsCalc {|
        calc_A_to_L := (Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0);
        calc_VAL := Z2B64 0
    |};
    RsCalc {|
        calc_A_to_L := (Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0,
                        Z2B64 0);
        calc_VAL := Z2B64 0
    |}
].

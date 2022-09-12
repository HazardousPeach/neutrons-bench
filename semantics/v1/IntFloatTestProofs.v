Require Import Flocq.Appli.Fappli_IEEE_bits.
Require Import List.
Import ListNotations.
Require Import ZArith.

Require Import v1.Epics.
Require Import v1.EpicsAux.
Require Import v1.Expr.
Require Import v1.FloatAux.
Require Import v1.MatchPres.
Require Import v1.Multi.
Require Import v1.NeutronTactics.
Require Import v1.Wf.
Require Import v1.FloatSpec.
Require Import v1.IntFloatTestDb.

Set Default Timeout 10.


Ltac clear_refl :=
    repeat match goal with
    | [ H : ?x = ?x |- _ ] => clear H
    end.

Definition my_spec := [
    ((REC_calc1, f_VAL), (0, 1)%Z);
    ((REC_calc2, f_VAL), (0, 1)%Z);
    ((REC_combine, f_A), (0, 1)%Z);
    ((REC_combine, f_B), (0, 1)%Z);
    ((REC_combine, f_VAL), (0, 2)%Z)
].


Open Scope Z.

Theorem spec_holds_start_in1 : forall rs,
    named_record_state my_dbs REC_in1 = Some rs ->
    spec_holds_record rs REC_in1 my_spec.
intros0 Hnrs. get_st.
Qed.

Theorem spec_holds_start_in2 : forall rs,
    named_record_state my_dbs REC_in2 = Some rs ->
    spec_holds_record rs REC_in2 my_spec.
intros0 Hnrs. get_st.
Qed.

Theorem spec_holds_start_calc1 : forall rs,
    named_record_state my_dbs REC_calc1 = Some rs ->
    spec_holds_record rs REC_calc1 my_spec.
intros0 Hnrs. get_st.

unfold spec_holds_record. intros0 Hrf Hrange.
destruct fn; unfold read_field in Hrf; try discriminate.
fancy_injection Hrf; subst; clear_refl.
compute in Hrange. inversion Hrange.
rp_subst.

exists 0. split; [ fwhole_eq_literal | omega ].
Qed.

Theorem spec_holds_start_calc2 : forall rs,
    named_record_state my_dbs REC_calc2 = Some rs ->
    spec_holds_record rs REC_calc2 my_spec.
intros0 Hnrs. get_st.

unfold spec_holds_record. intros0 Hrf Hrange.
destruct fn; unfold read_field in Hrf; try discriminate.
fancy_injection Hrf; subst; clear_refl.
compute in Hrange. inversion Hrange.
rp_subst.

exists 0. split; [ fwhole_eq_literal | omega ].
Qed.

Theorem spec_holds_start_combine : forall rs,
    named_record_state my_dbs REC_combine = Some rs ->
    spec_holds_record rs REC_combine my_spec.
intros0 Hnrs. get_st.

unfold spec_holds_record. intros0 Hrf Hrange.
destruct fn; unfold read_field in Hrf; try discriminate; [ | unroll_index i ];
match type of Hrf with Some (VDouble ?x) = Some (VDouble ?y) =>
        assert (x = y) by congruence end;
compute in Hrange; inversion Hrange;
rp_subst.

- exists 0. split; [ fwhole_eq_literal | omega ].
- exists 0. split; [ fwhole_eq_literal | omega ].
- exists 0. split; [ fwhole_eq_literal | omega ].
Qed.

Lemma named_record_config_lt_length : forall dbc rn rc,
    named_record_config dbc rn = Some rc ->
    (rn < length dbc)%nat.
first_induction dbc; intros0 Hnrc.
{ discriminate Hnrc. }

destruct rn.
- simpl. omega.
- simpl. simpl in Hnrc.
  forward eapply IHdbc; eauto.
  omega.
Qed.

Lemma named_record_state_lt_length : forall dbs rn rs,
    named_record_state dbs rn = Some rs ->
    (rn < length dbs)%nat.
first_induction dbs; intros0 Hnrs.
{ discriminate Hnrs. }

destruct rn.
- simpl. omega.
- simpl. simpl in Hnrs.
  forward eapply IHdbs; eauto.
  omega.
Qed.

Lemma process_rn_lt_length : forall dbc dbs rn p dbs' oes,
    process dbc dbs rn p dbs' oes ->
    (rn < length dbc)%nat.
intros0 Hproc.
inversion Hproc; unmangle_process; subst;
eauto using named_record_config_lt_length.
Qed.

Theorem spec_holds_start : spec_holds my_dbs my_spec.
unfold spec_holds. intros.
assert (Hlt : (rn < length my_dbs)%nat) by eauto using named_record_state_lt_length.
simpl in Hlt.

let rec go := destruct rn; [ | omega || go ] in go;
eauto using
    spec_holds_start_in1,
    spec_holds_start_in2,
    spec_holds_start_calc1,
    spec_holds_start_calc2,
    spec_holds_start_combine.
Qed.




Ltac unpack_calc_Hpp calc_INPA_to_INPL :=
    let il := fresh "il" in
    let Heqil := fresh "Heqil" in
    let Hpp := fresh "Hpp" in
    intros il ?dbs ?p ?dbs' ?oes Heqil Hpp ?Hspec ?Hproc;
    match goal with [ H : _ = calc_INPA_to_INPL |- _ ] =>
            rewrite <- H in Heqil end;
    simpl in Heqil; try discriminate Heqil;
    fancy_injection Heqil; subst il; clear_refl;
    simpl in Hpp; try discriminate Hpp;
    clear Hpp.

Ltac unpack_calc_HA2L calc_INPA_to_INPL :=
    let il := fresh "il" in
    let Heqil := fresh "Heqil" in
    intros il ?x Heqil;
    match goal with [ H : _ = calc_INPA_to_INPL |- _ ] =>
            rewrite <- H in Heqil end;
    simpl in Heqil; try discriminate Heqil;
    fancy_injection Heqil; subst il; clear_refl;
    unfold il_rn, il_fn, il_pp in *;
    unfold denote_field_spec; (break_match; eauto);
    compute_spec_range; try compute_spec_range;
    unfold denote_range; eauto.

Ltac unpack_calc_Hflnk calc_FLNK :=
    let fl := fresh "fl" in
    let Heqfl := fresh "Heqfl" in
    intros fl ?dbs ?p ?dbs' ?oes Heqfl ?Hspec ?Hproc;
    match goal with [ H : _ = calc_FLNK |- _ ] =>
            rewrite <- H in Heqfl end;
    simpl in Heqfl; try discriminate Heqfl;
    fancy_injection Heqfl; subst fl; clear_refl;
    unfold fl_rn in *.

Ltac unpack_calc_Hcalc calc_CALC :=
    let Hspec := fresh "Hspec" in
    let calc_A_to_L := fresh "calc_A_to_L" in
    intros (calc_A_to_L, ?) Hspec;

    let a := fresh "a" in
    let Heqa2l := fresh "Heqa2l" in
    destruct calc_A_to_L as [[[[[[[[[[[a ?b] ?c] ?d] ?e] ?f] ?g] ?h] ?i] ?j] ?k] ?l] eqn:Heqa2l;
    simpl in a; (* fix type:  multi 1 e_double  ->  e_double *)

    (* generate hypotheses about field A .. L *)
    for_index 12%nat, (fun i => 
        match type of Heqa2l with
        | _ = ?a2l =>
            (* get the name (a .. l) of the relevant variable, and use it to
             * give the hypothesis a nice name *)
            let v := eval simpl in ((a2l : multi 12 _) !! $(mk_index i)$) in
            let H := fresh Hspec "_" v  in
            set (H := Hspec $(mk_index i)$);
            clearbody H; simpl in H;
            (* clear trivial hypotheses arising from unconstrained fields *) 
            match type of H with | True => clear H | _ => idtac end
        end);

    let a2l' := fresh "a2l'" in
    let val' := fresh "val'" in
    let Heqcalc := fresh "Heqcalc" in
    unfold Epics0.calc_CALC;
    destruct (calc_CALC _) as (a2l', val') eqn:Heqcalc;
    subst calc_CALC; simpl in Heqcalc;
    fancy_injection Heqcalc;
    subst a2l'; subst val'; clear Heqcalc;

    split;
    [ let i := fresh "i" in
      intro i; unroll_index i; simpl; eauto
    | simpl ];

    idtac.

Theorem spec_holds_process_combine : forall dbs p oes dbs',
    spec_holds dbs my_spec ->
    process my_dbc dbs REC_combine p dbs' oes ->
    spec_holds dbs' my_spec.
get_cfg' my_dbc REC_combine.
(* TODO *)
destruct (CalcConfig _ _ _) eqn:?. fancy_injection Heqc.

intros0 Hdm Hspec_ Hproc.
eapply spec_holds_process_calc; try eassumption; unfold_field_projections.

- unroll_index i; unpack_calc_Hpp calc_INPA_to_INPL.
- unroll_index i; unpack_calc_HA2L calc_INPA_to_INPL.
- unpack_calc_Hflnk calc_FLNK.
- unpack_calc_Hcalc calc_CALC.
  + simpl. 
    destruct Hspec_a as (z_a & ? & ?).
    destruct Hspec_b as (z_b & ? & ?).
    exists (z_a + z_b).
    split; [ | omega ].
    eapply fwhole_eq_Bplus; eauto.
    assert (2 < 2^(53 - 1)).
    { replace 2 with (2^1) at 1 by reflexivity. eapply Z.pow_lt_mono_r; omega. }
    rewrite Z.abs_eq by omega.
    omega.
Qed.

Theorem spec_holds_process_calc1 : forall dbs p oes dbs',
    spec_holds dbs my_spec ->
    process my_dbc dbs REC_calc1 p dbs' oes ->
    spec_holds dbs' my_spec.
get_cfg' my_dbc REC_calc1.
destruct (CalcConfig _ _ _) eqn:?. fancy_injection Heqc.

intros0 Hdm Hspec Hproc.
eapply spec_holds_process_calc; try eassumption; unfold_field_projections.

- unroll_index i; unpack_calc_Hpp calc_INPA_to_INPL.
- unroll_index i; unpack_calc_HA2L calc_INPA_to_INPL.
- unpack_calc_Hflnk calc_FLNK.
  eauto using spec_holds_process_combine.
- unpack_calc_Hcalc calc_CALC.
  + simpl.  break_exists.  break_and.
    unfold b64_lt.
    break_match; [ break_match | ];
            eexists; (split; [ fwhole_eq_literal | omega ]).
Qed.

Theorem spec_holds_process_calc2 : forall dbs p oes dbs',
    spec_holds dbs my_spec ->
    process my_dbc dbs REC_calc2 p dbs' oes ->
    spec_holds dbs' my_spec.
get_cfg' my_dbc REC_calc2.
destruct (CalcConfig _ _ _) eqn:?. fancy_injection Heqc.

intros0 Hdm Hspec Hproc.
eapply spec_holds_process_calc; try eassumption; unfold_field_projections.

- unroll_index i; unpack_calc_Hpp calc_INPA_to_INPL.
- unroll_index i; unpack_calc_HA2L calc_INPA_to_INPL.
- unpack_calc_Hflnk calc_FLNK.
  eauto using spec_holds_process_combine.
- unpack_calc_Hcalc calc_CALC.
  + simpl.  break_exists.  break_and.
    unfold b64_lt.
    break_match; [ break_match | ];
            eexists; (split; [ fwhole_eq_literal | omega ]).
Qed.

Theorem spec_holds_process_in1 : forall dbs p oes dbs',
    spec_holds dbs my_spec ->
    process my_dbc dbs REC_in1 p dbs' oes ->
    spec_holds dbs' my_spec.
get_cfg' my_dbc REC_in1.
destruct (AnalogInConfig _) eqn:?. fancy_injection Heqa.

intros0 Hdm Hspec Hproc.
eapply spec_holds_process_analog_in; try eassumption; unfold_field_projections.

- unpack_calc_Hflnk analog_in_FLNK.
  eauto using spec_holds_process_calc1.
Qed.

Theorem spec_holds_process_in2 : forall dbs p oes dbs',
    spec_holds dbs my_spec ->
    process my_dbc dbs REC_in2 p dbs' oes ->
    spec_holds dbs' my_spec.
get_cfg' my_dbc REC_in2.
destruct (AnalogInConfig _) eqn:?. fancy_injection Heqa.

intros0 Hdm Hspec Hproc.
eapply spec_holds_process_analog_in; try eassumption; unfold_field_projections.

- unpack_calc_Hflnk analog_in_FLNK.
  eauto using spec_holds_process_calc2.
Qed.

Theorem spec_holds_process : forall dbs rn p oes dbs',
    spec_holds dbs my_spec ->
    process my_dbc dbs rn p dbs' oes ->
    spec_holds dbs' my_spec.
intros0 Hspec Hproc.
assert (Hlt : (rn < length my_dbc)%nat) by eauto using process_rn_lt_length.
simpl in Hlt.

let rec go := destruct rn; [ | omega || go ] in go;
eauto 2 using
    spec_holds_process_in1,
    spec_holds_process_in2,
    spec_holds_process_calc1,
    spec_holds_process_calc2,
    spec_holds_process_combine.
Qed.

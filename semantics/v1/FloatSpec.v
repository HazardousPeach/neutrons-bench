Require Import Arith.
Require Import List.
Import ListNotations.
Require Import ZArith.

Require Import v1.FloatAux.

Require Import v1.NeutronTactics.
Require Import v1.Util.
Require Import v1.Multi.
Require Import v1.ListLemmas.
Require Import v1.Wf.
Require Import v1.Terminate.
Require Import v1.Preservation.

Require Import v1.EpicsTypes.
Require Import v1.EpicsRecords.
Require Import v1.Step.
Require Import v1.StepAux.

Set Default Timeout 10.


(* "Field `fn` of record `rn` should contain a double that represents a whole
 * number `z` where `min <= z <= max`." *)
Definition spec_item := ((record_name * field_name) * (Z * Z))%type.
Definition spec := list spec_item.


Definition spec_key_eq_dec (rfn1 rfn2 : (record_name * field_name)) :
    { rfn1 = rfn2 } + { rfn1 <> rfn2 }.
destruct rfn1, rfn2.
destruct (eq_nat_dec r r0); [ subst | right; congruence ].
destruct (field_name_eq_dec f f0); [ subst | right; congruence ].
left. reflexivity.
Defined.


(* Get the range for a record and field, or None if the spec does not constrain
 * that record/field. *)
Fixpoint spec_range s rn fn : option (Z * Z) :=
    match s with
    | [] => None
    | (k, r) :: s' =>
            if spec_key_eq_dec k (rn, fn) then Some r else spec_range s' rn fn
    end.


(* Proposition: there is no entry for `(rn, fn)` in `s`. *)
Definition spec_no_entry rn fn s :=
    Forall (fun (i : spec_item) => let (k, r) := i in k <> (rn, fn)) s.

Lemma spec_range_no_entry : forall rn fn s,
    spec_no_entry rn fn s ->
    spec_range s rn fn = None.
first_induction s; intros0 Hno; simpl.
{ reflexivity. }
break_match. break_match.
- inversion Hno. firstorder.
- eapply IHs. unfold spec_no_entry in Hno. inversion Hno. assumption.
Qed.

(* Check that the spec is internally consistent: all entries have unique keys,
 * and all ranges have min <= max. *)
Inductive spec_ok : spec -> Prop :=
| SoNil : spec_ok []
| SoCons : forall rn fn min max s,
        spec_no_entry rn fn s ->
        (min <= max)%Z ->
        spec_ok (((rn, fn), (min, max)) :: s).


(* Proposition: For every double-valued field `fn` in `rs`, the value satisfies
 * the requirements of spec `s` for `(rn, fn)`.  (In other words, `rs` is a
 * valid state for record `rn` according to spec `s`.) *)
Definition spec_holds_record rs rn s :=
    forall fn f min max,
        read_field rs fn = Some (VDouble f) ->
        spec_range s rn fn = Some (min, max) ->
        exists z,
            fwhole_eq f z /\
            (min <= z <= max)%Z.

Definition spec_holds dbs s :=
    forall rn rs,
        lookup_state dbs rn = Some rs ->
        spec_holds_record rs rn s.


Definition denote_range opt_r (x : e_double) :=
    match opt_r with
    | None => True
    | Some (min, max) =>
            exists z, fwhole_eq x z /\ (min <= z)%Z /\ (z <= max)%Z
    end.

Definition denote_field_spec s rn fn val :=
    match val with
    | VDouble x => denote_range (spec_range s rn fn) x
    | _ => True
    end.

Lemma range_lookup_state : forall s dbs rn rs,
    spec_holds dbs s ->
    lookup_state dbs rn = Some rs ->
    spec_holds_record rs rn s.
intros0 Hspec Hlook.
eauto.
Qed.

(*
Lemma range_lookup_state : forall s dbs rn rs fn val,
    spec_holds dbs s ->
    lookup_state dbs rn = Some rs ->
    read_field rs fn = Some val ->
    denote_field_spec s rn fn val.
intros0 Hspec Hrf Hlook.
destruct val; simpl; eauto.
destruct (spec_range _ _ _) as [ [ min max ] | ] eqn:?; simpl; eauto.
eapply Hspec; eauto.
Qed.
*)

Lemma range_read_field : forall s rs fn val rn,
    spec_holds_record rs rn s ->
    read_field rs fn = Some val ->
    denote_field_spec s rn fn val.
intros0 Hspec Hrf.
unfold spec_holds_record in Hspec.
unfold denote_field_spec. destruct val; eauto.
destruct (spec_range _ _ _) as [ [min max] | ] eqn:?.
- eapply Hspec; eauto.
- simpl. eauto.
Qed.

Lemma range_read_record_field : forall s dbs rn fn val,
    spec_holds dbs s ->
    read_record_field dbs rn fn = Some val ->
    denote_field_spec s rn fn val.
intros0 Hspec Hrrf.
unfold read_record_field, bind_option in Hrrf.
break_match; try discriminate.
forward eapply range_lookup_state; eauto.
eapply range_read_field; eauto.
Qed.

Ltac inject_some := repeat on (Some _ = Some _), invc.
Ltac inject_pair := repeat on ((_, _) = (_, _)), invc.

Ltac break_bind_option :=
    repeat match goal with
    | [ H : bind_option ?x _ = Some _ |- _ ] =>
            destruct x eqn:?;
                    [ unfold bind_option at 1 in H
                    | discriminate H ]
    end.

Require Import ProofIrrelevance.

Lemma write_field_read_field_same : forall rs fn rs' val',
    write_field rs fn val' = Some rs' ->
    read_field rs' fn = Some val'.
intros0 Hwf.

all: destruct fn; destruct_record rs as [ st ];
    unfold write_field in Hwf; try discriminate Hwf.
(* get rid of bogus `tmp` cases *)
all: try (destruct n; try discriminate Hwf).
all: try break_bind_option.

all: fancy_injr <- Hwf; unfold read_field.
all: destruct st; compute -[multi_get multi_set]; simpl in * |-.
all: try rewrite multi_set_get by reflexivity.

all: destruct val'; try discriminate;
    unfold unwrap_double, unwrap_string, unwrap_enum, unwrap_long, unwrap_array in *.
(* double, string, long *)
all: try solve [invc Heqo; reflexivity].
(* enum *)
all: try solve [break_match; try discriminate; inject_some;
    unfold eq_rect_r; rewrite <- eq_rect_eq; reflexivity].
(* array *)
all: try solve [
    break_match; try discriminate;
    break_match; try discriminate; invc Heqo;
    unfold eq_rect_r; do 2 rewrite <- eq_rect_eq; reflexivity].
Qed.

Lemma write_field_read_field_eq : forall rs fn1 fn2 rs' val',
    field_name_eq fn1 fn2 ->
    write_field rs fn2 val' = Some rs' ->
    read_field rs' fn1 = Some val'.
intros0 Heq Hwf.
invc Heq; [ destruct fn2 | .. ];
(destruct_record rs as [ st ]; unfold write_field in Hwf; try discriminate);
(destruct st; destruct val'; try discriminate);
(unfold unwrap_double, unwrap_string, unwrap_bool, bind_option in Hwf;
  symmetry in Hwf; fancy_injr Hwf);
(unfold read_field; try rewrite multi_set_get; congruence).
Qed.

Lemma write_field_read_field_ne' : forall rs fn1 fn2 rs' val val',
    (~field_name_eq fn1 fn2) ->
    write_field rs fn2 val' = Some rs' ->
    read_field rs fn1 = Some val ->
    read_field rs' fn1 = Some val.
intros0 Heq Hwf Hrf.
(destruct fn2; destruct_record rs as [ st ]; unfold write_field in Hwf; try discriminate);
(destruct st; destruct val'; try discriminate);
(unfold unwrap_double, unwrap_string, unwrap_bool, bind_option in Hwf;
  symmetry in Hwf; fancy_injr Hwf);
(destruct fn1; try solve [ discriminate Hrf | contradict Heq; econstructor; eauto ]);
(unfold read_field in *;
  try erewrite multi_set_get_other by (contradict Heq; econstructor; solve [ eauto ]);
  try solve [ rewrite Hrf; reflexivity ]).
- admit. (* H_DBL *)
- admit. (* H_STR *)
- admit. (* H_BOOL *)
Admitted.

Lemma write_field_read_field_ne : forall rs fn1 fn2 rs' val',
    (~field_name_eq fn1 fn2) ->
    write_field rs fn2 val' = Some rs' ->
    read_field rs fn1 = read_field rs' fn1.
intros0 Heq Hwf.
destruct (read_field _ _) eqn:?.
{ forward eapply write_field_read_field_ne'; eauto. }

forward eapply write_field_preserves_state_type as Hty; eauto.
destruct_record rs as [ st ]; destruct_record rs' as [ st' ]; try discriminate Hty;
destruct fn1; unfold read_field in *;
try reflexivity; destruct st; try discriminate.

(* TODO: will go away once record_type covers all record_state variants *)
all:try solve [exfalso; eapply no_record_type_nex; eauto].
Qed.

Lemma range_write_field : forall s rs fn val rs' rn,
    denote_field_spec s rn fn val ->
    spec_holds_record rs rn s ->
    write_field rs fn val = Some rs' ->
    spec_holds_record rs' rn s.
intros0 Hval Hspec Hwf.
unfold spec_holds_record, denote_field_spec in *.
intros0 Hrf Hrange.
destruct (field_name_eq_dec fn0 fn).

- forward eapply write_field_read_field_eq; eauto.
  destruct val; try congruence. equate in type e_double by congruence.
  unfold denote_range in Hval.
  erewrite spec_range_eq in Hval by eauto using field_name_eq_symm.
  rewrite Hrange in Hval. assumption.

- eapply Hspec with (fn := fn0); try eassumption.
  erewrite write_field_read_field_ne; eauto.
Qed.

Lemma update_record_lookup_eq : forall f dbs rn dbs' rs rs',
    update_record f dbs rn = Some dbs' ->
    lookup dbs rn = Some rs ->
    f rs = Some rs' ->
    lookup dbs' rn = Some rs'.
first_induction rn; intros0 Hup Hlook Hf.

- destruct dbs as [ | rs0 dbs ]; try discriminate Hlook.
  simpl in Hlook. fancy_injr Hlook.
  unfold update_record in Hup. rewrite Hf in Hup.

  destruct dbs' as [ | rs'0 dbs' ]; try congruence.
  replace rs'0 with rs' in * by congruence.

  simpl. reflexivity.

- destruct dbs as [ | rs0 dbs ]; try discriminate Hlook.
  simpl in Hlook.

  simpl in Hup. break_match; try congruence.
  fancy_injr <- Hup. simpl.

  eapply IHrn; eauto.
Qed.

Lemma update_record_lookup_eq' : forall f dbs rn dbs' rs,
    update_record f dbs rn = Some dbs' ->
    lookup dbs rn = Some rs ->
    lookup dbs' rn = f rs.
first_induction rn; intros0 Hup Hlook.

- destruct dbs as [ | rs0 dbs ]; try discriminate Hlook.
  simpl in Hlook. fancy_injr Hlook.
  unfold update_record in Hup. destruct (f rs) as [ rs' | ] eqn:?; try discriminate.
  fancy_injr <- Hup. simpl.
  reflexivity.

- destruct dbs as [ | rs0 dbs ]; try discriminate Hlook.
  simpl in Hlook.

  simpl in Hup. break_match; try congruence.
  fancy_injr <- Hup. simpl.

  eapply IHrn; eauto.
Qed.

Lemma update_record_lookup_ne : forall f dbs rn dbs' rn',
    update_record f dbs rn = Some dbs' ->
    rn <> rn' ->
    lookup dbs rn' = lookup dbs' rn'.
first_induction rn; intros0 Hup Hne.

- destruct dbs; simpl in Hup; try congruence.
  break_match; try congruence.
  destruct rn'; try congruence.
  fancy_injr <- Hup. simpl.
  reflexivity.

- destruct dbs; simpl in Hup; try congruence.
  break_match; try congruence.
  fancy_injr <- Hup.

  destruct rn'.
  + simpl. reflexivity.
  + simpl. eapply IHrn; eauto.
Qed.

Lemma update_record_lookup_or : forall f dbs rn dbs' rn' rs,
    update_record f dbs rn = Some dbs' ->
    lookup dbs rn' = Some rs ->
    lookup dbs' rn' = Some rs \/ lookup dbs' rn' = f rs.
intros0 Hup Hlook.
destruct (eq_nat_dec rn rn').

- (* equal *)
  right. subst. eauto using update_record_lookup_eq'.

- (* not equal *)
  left. erewrite <- update_record_lookup_ne; eauto.
Qed.

Lemma update_record_Some_lt : forall f dbs rn dbs',
    update_record f dbs rn = Some dbs' ->
    rn < length dbs.
first_induction rn; intros0 Hup.

- destruct dbs; try discriminate Hup.
  simpl. omega.

- destruct dbs; try discriminate Hup.
  simpl in Hup. break_match; try discriminate.
  forward eapply IHrn; eauto.
  simpl. omega.
Qed.

Lemma update_record_preserves_length : forall f dbs rn dbs',
    update_record f dbs rn = Some dbs' ->
    length dbs' = length dbs.
first_induction rn; intros0 Hup;
destruct dbs; try discriminate Hup.

- unfold update_record in Hup.
  break_match; try discriminate.
  fancy_injr <- Hup. simpl.
  reflexivity.

- simpl in Hup.
  break_match; try discriminate.
  fancy_injr <- Hup. simpl.
  erewrite IHrn; eauto.
Qed.

Lemma range_update_record : forall s f dbs rn dbs',
    (forall rs rs',
        spec_holds_record rs rn s ->
        f rs = Some rs' ->
        spec_holds_record rs' rn s) ->
    spec_holds dbs s ->
    update_record f dbs rn = Some dbs' ->
    spec_holds dbs' s.
(*make_first rn; induction rn eqn:Heqrn*)
intros0 Hf Hspec Hup.

unfold spec_holds. intros0 Hlook.

forward eapply lookup_length_ex with (ys := dbs) as [ rs0 Hrs0 ]; eauto.
{ eapply update_record_preserves_length; eauto. }

destruct (eq_nat_dec rn rn0).

- subst rn0.
  forward eapply update_record_lookup_eq' as Hup'; eauto.
  eapply Hf with (rs := rs0).
  + eapply Hspec. congruence.
  + congruence.

- forward eapply update_record_lookup_ne as Hup'; eauto.
  eapply Hspec. congruence.
Qed.

Lemma range_write_record_field : forall s dbs rn fn val dbs',
    denote_field_spec s rn fn val ->
    spec_holds dbs s ->
    write_record_field dbs rn fn val = Some dbs' ->
    spec_holds dbs' s.
intros0 Hval Hspec Hwrf.
unfold write_record_field in Hwrf.
eapply range_update_record; eauto.

cbv beta. intros0 Hrspec Hwf.
eapply range_write_field; eauto.
Qed.


Lemma range_db_step_set_const : forall s dbs rn dbs'  fn val,
    denote_field_spec s rn fn val ->
    spec_holds dbs s ->
    db_step rn (MSetConst fn val) dbs dbs' ->
    spec_holds dbs' s.
intros0 Hop Hspec Hstep. invc Hstep.
eapply range_write_record_field; eauto.
Qed.

Lemma range_db_step_read_link : forall s dbs rn dbs'  il il_ty fn f_ty,
    (forall val val',
        denote_field_spec s (il_rn il) (il_fn il) val ->
        value_type val = il_ty ->
        convert_value val f_ty = Some val' ->
        denote_field_spec s rn fn val') ->
    spec_holds dbs s ->
    db_step rn (MReadLink il il_ty fn f_ty) dbs dbs' ->
    spec_holds dbs' s.
intros0 Hop Hspec Hstep. invc Hstep.
eapply range_write_record_field; eauto.
eapply Hop; eauto.
eapply range_read_record_field; eauto.
Qed.

Lemma range_db_step_write_link : forall s dbs rn dbs'  fn f_ty ol ol_ty,
    (forall val val',
        denote_field_spec s rn fn val ->
        value_type val = f_ty ->
        convert_value val ol_ty = Some val' ->
        denote_field_spec s (ol_rn ol) (ol_fn ol) val') ->
    spec_holds dbs s ->
    db_step rn (MWriteLink fn f_ty ol ol_ty) dbs dbs' ->
    spec_holds dbs' s.
intros0 Hop Hspec Hstep. invc Hstep.
eapply range_write_record_field; eauto.
eapply Hop; eauto.
eapply range_read_record_field; eauto.
Qed.

Lemma range_db_step_calculate : forall s dbs rn dbs'  expr fn_out,
    True (* TODO *) ->
    spec_holds dbs s ->
    db_step rn (MCalculate expr fn_out) dbs dbs' ->
    spec_holds dbs' s.
intros0 Hop Hspec Hstep. invc Hstep.
admit.
Admitted.


Definition micro_range_ok s rn op :=
    is_db_op op = true ->
    forall dbs dbs',
    spec_holds dbs s ->
    db_step rn op dbs dbs' ->
    spec_holds dbs' s.

Definition program_range_ok s rn rp :=
    Forall (micro_range_ok s rn) (rp_code rp).

Definition database_range_ok s dbp :=
    forall rn rp,
    lookup dbp rn = Some rp ->
    program_range_ok s rn rp.

Definition frame_range_ok s frame :=
    Forall (micro_range_ok s (frame_rn frame)) (frame_code frame).

Definition state_range_ok s state :=
    Forall (frame_range_ok s) (state_stk state).

Definition spec_holds_state state s :=
    spec_holds (state_dbs state) s.


Lemma range_db_step : forall s rn op dbs dbs',
    micro_range_ok s rn op ->
    spec_holds dbs s ->
    db_step rn op dbs dbs' ->
    spec_holds dbs' s.
intros0 Hrange Hspec Hstep.
eapply Hrange; eauto.
invc Hstep; simpl; reflexivity.
Qed.

Theorem range_step : forall s dbp state state',
    state_range_ok s state ->
    spec_holds_state state s ->
    step dbp state state' ->
    spec_holds_state state' s.
intros0 Hrng_st Hspec Hstep. invc Hstep.

- (* SDb *)
  unfold spec_holds_state, state_dbs in *.
  eapply range_db_step; eauto.
  invc Hrng_st.
  on (frame_range_ok _ _), invc.
  unfold frame_rn in *. assumption.

- (* SPop *)
  unfold spec_holds_state, state_dbs in *.
  assumption.

- (* SProcess *)
  unfold spec_holds_state, state_dbs in *.
  assumption.
Qed.

Lemma lookup_Forall : forall A xs idx x (P : A -> Prop),
    Forall P xs ->
    lookup xs idx = Some x ->
    P x.
first_induction idx; intros0 Hfa Hlook;
invc Hfa; simpl in Hlook; try discriminate Hlook.
- congruence.
- eapply IHidx; eauto.
Qed.

Lemma lookup_program_range_ok : forall s dbp rn rp,
    database_range_ok s dbp ->
    lookup dbp rn = Some rp ->
    program_range_ok s rn rp.
intros0 Hrng Hlook.
eapply Hrng. assumption.
Qed.

Theorem range_step_ok : forall s dbp state state',
    database_range_ok s dbp ->
    state_range_ok s state ->
    spec_holds_state state s ->
    step dbp state state' ->
    state_range_ok s state'.
intros0 Hrng_db Hrng_st Hspec Hstep. invc Hstep.

- (* SDb *)
  unfold state_range_ok, state_stk in *.
  invc Hrng_st. constructor; eauto.
  unfold frame_range_ok, frame_rn, frame_code in *.
  on (Forall (micro_range_ok _ _) _), invc.
  assumption.

- (* SPop *)
  unfold state_range_ok, state_stk in *.
  invc Hrng_st.
  assumption.

- (* SProcess *)
  unfold state_range_ok, state_stk in *.
  invc Hrng_st.
  constructor; cycle 1.
  { constructor; [ | assumption ]. on >frame_range_ok, invc.
    unfold frame_range_ok, frame_rn, frame_code. assumption. }
  forward eapply lookup_program_range_ok; eauto.
Qed.



(* TODO TODO *)



Lemma range_read_in_link : forall s dbc dbs il p dbs' oes val,
    (il_pp il = PP ->
        spec_holds dbs s ->
        process dbc dbs (il_rn il) p dbs' oes ->
        spec_holds dbs' s) ->
    spec_holds dbs s ->
    read_in_link dbc dbs il p dbs' oes val ->
    denote_field_spec s (il_rn il) (il_fn il) val.
intros0 Hpp Hspec Hril.
inversion Hril. unmangle_process. subst.

destruct (il_pp il).
- with process_passive hyp, eta_inversion. unmangle_process. subst.
  forward eapply Hpp; eauto.
  eapply range_lookup_state; eauto.
- with process_passive hyp, eta_inversion. unmangle_process. subst.
  eapply range_lookup_state; eauto.
Qed.


(* Helper tactics *)
Ltac get_st :=
    match goal with
    | [ H : named_record_state ?dbs ?rn = Some ?rs |- _ ] =>
            try unfold dbs in H; try unfold rn in H; compute [named_record_state] in H;
            let st := fresh "st" in
            destruct_record rs as [ st ]; try discriminate; destruct st;
            match type of H with
            | Some (?ctor ?x) = Some (?ctor ?y) =>
                    let H' := fresh in
                    assert (H' : y = x) by congruence;
                    fancy_injr H';
                    clear H
            end
    end.

Ltac get_cfg :=
    match goal with
    | [ H : named_record_config ?dbc ?rn = Some (?Ctor ?cfg) |- _ ] =>
            try unfold dbc in H; try unfold rn in H; compute [named_record_config] in H;
            destruct cfg;
            match type of H with
            | Some (?ctor ?x) = Some (?ctor ?y) =>
                    let H' := fresh in
                    assert (H' : y = x) by congruence;
                    fancy_injr H';
                    clear H
            end
    end.

Ltac get_cfg' dbc rn :=
    let rc_val := eval compute [dbc rn named_record_config] in (named_record_config dbc rn) in
    let rc := fresh "rc" in
    match rc_val with
    | Some ?x =>
            set (rc := x);
            assert (named_record_config dbc rn = Some rc) by reflexivity
    end.

Ltac rp_subst := repeat progress subst.

Ltac unroll_index i :=
    let i' := fresh "i'" in
    let rec go := first [ exfalso; omega | destruct i'; [ | go ] ] in
    destruct i as [ i' ?Hlt ]; go.

Tactic Notation "for_index" constr(n) "," tactic3(tac) :=
    let n := eval compute in n in
    match n with
    | O => idtac
    | S _ => idtac
    | _ => let T := type of n in fail "expected a nat literal, not" n "(" T ")"
    end;
    let rec go i :=
        let i := eval compute in i in
        lazymatch i with
        | 100%nat => fail 2 "too many!"
        | n => idtac
        | _ => tac i; go (S i)
        end in
    go 0%nat.

Ltac unfold_field_projections :=
    unfold
        Epics0.calc_INPA_to_INPL,
        Epics0.calc_FLNK,
        Epics0.calc_A_to_L,
        Epics0.calc_VAL
        in *.

Ltac compute_spec_range :=
    let min := fresh "min" in
    let max := fresh "max" in
    let Hrange := fresh "Hrange" in
    destruct (spec_range _ _ _) as [ [ min max ] | ] eqn:Hrange;
        compute in Hrange; inversion Hrange; try subst min max; clear Hrange.


(* propagate_spec_holds and helpers *)
Ltac clear_after H :=
    let T := type of H in
    repeat lazymatch goal with
    | [ H' : ?T' |- _ ] =>
            lazymatch T' with
            | T => fail
            | _ => clear H'
            end
    end.

Ltac real_move_before H H' :=
    move H at top; move H before H'.

Ltac real_move_after H H' :=
    move H at top; move H after H'.

Ltac propagate_spec_holds1 :=
    let go_extra Hspec s Hwork dbs' extra :=
        let Hspec_old := fresh Hspec "_old0" in
        rename Hspec into Hspec_old; real_move_before Hspec_old Hwork;
        assert (Hspec : spec_holds dbs' s);
        [ rename Hspec_old into Hspec
        | real_move_after Hspec Hwork; extra ]
    in
    let go Hspec s Hwork dbs' := go_extra Hspec s Hwork dbs' ltac:idtac in
    lazymatch goal with
    | [ Hspec : spec_holds ?dbs ?s |- _ ] =>
            let go' := go Hspec s in
            lazymatch goal with
            | [ H : do_indexed _ dbs ?dbs' _ |- _ ] => go' H dbs'
            | [ H : update_record _ dbs _ = Some ?dbs' |- _ ] => go' H dbs'
            | [ H : process_opt_fwd_link _ dbs _ _ ?dbs' _ |- _ ] => go' H dbs'
            (* read_in_link gets special handling *)
            | [ H : read_in_link _ dbs ?il _ ?dbs' _ ?val |- _ ] =>
                    go_extra Hspec s H dbs' ltac:(
                        assert (denote_field_spec s (il_rn il) (il_fn il) val);
                        eauto using range_read_in_link)
            end
    end.

Ltac propagate_spec_holds :=
    propagate_spec_holds1; [ .. | try assumption; try propagate_spec_holds ].


(* Misc helper lemmas about Zs and doubles *)

Definition Z_size z :=
    match z with
    | Z0 => Z.of_N (N.size N0)
    | Zpos p => Z.of_N (N.size (N.pos p))
    | Zneg p => Z.of_N (N.size (N.pos p))
    end.

Lemma Z_abs_size_bound : forall z e, (Z_size z <= e -> Z.abs z < 2 ^ e)%Z.
intros0 Hle.

destruct (Z.eq_dec z 0).
{ subst z. simpl in *. eapply Z.pow_pos_nonneg; omega. }

replace (Z_size z) with (Z.succ (Z.log2 (Z.abs z))) in Hle; cycle 1.
{ unfold Z_size. destruct z; try congruence; unfold Z.abs.
  all: rewrite N.size_log2 by congruence.
  all: rewrite N2Z.inj_succ.
  all: unfold Z.log2, N.log2.
  all: destruct p; simpl; reflexivity. }
forward eapply (Z.log2_nonneg (Z.abs z)).
forward eapply (Z.log2_spec (Z.abs z)) as [Hmin Hmax].
{ eapply Z.abs_pos. assumption. }
rewrite (Z.pow_le_mono_r_iff 2) in Hle; omega.
Qed.

Ltac fwhole_eq_literal :=
    eapply fwhole_eq_Z2B, Z_abs_size_bound;
    compute; congruence.


(* Helper lemmas about Epics *)

(* named_record_state *)
Lemma named_record_state_lt : forall dbs rn rs,
    named_record_state dbs rn = Some rs ->
    (rn < length dbs)%nat.
first_induction dbs; intros0 Heq; simpl in Heq.
{ congruence. }

destruct rn.
- simpl. omega.
- simpl. forward eapply IHdbs; eauto. omega.
Qed.

Lemma lt_named_record_state : forall dbs rn,
    (rn < length dbs)%nat ->
    exists rs, named_record_state dbs rn = Some rs.
first_induction dbs; intros0 Heq; simpl in Heq.
{ omega. }

destruct rn.
- simpl. eexists. reflexivity.
- eapply IHdbs. omega.
Qed.

(* update_record *)
Lemma update_record_lookup : forall f dbs rn rs dbs' rs',
    update_record f dbs rn = Some dbs' ->
    named_record_state dbs rn = Some rs ->
    named_record_state dbs' rn = Some rs' ->
    f rs = Some rs'.
first_induction dbs; intros0 Hupd Hnrs Hnrs'.
{ (* empty list *) simpl in Hupd. congruence. }

simpl in Hupd. break_match.
- (* rn = 0 *)
  break_match; try congruence.
  destruct dbs'; try congruence.
  simpl in Hnrs, Hnrs'. congruence.
- (* rn = S _ *)
  break_match; try congruence.
  destruct dbs'; try congruence.
  fancy_injr Hupd.
  simpl in Hnrs, Hnrs'.
  eapply IHdbs; eauto.
Qed.

Lemma update_record_lookup_other : forall f dbs rn rn' dbs',
    rn <> rn' ->
    update_record f dbs rn = Some dbs' ->
    named_record_state dbs rn' = named_record_state dbs' rn'.
first_induction dbs; intros0 Hne Hupd.
{ (* empty list *) simpl in Hupd. congruence. }

simpl in Hupd. break_match.
- (* rn = 0 *)
  break_match; try congruence.
  destruct dbs'; try congruence.
  destruct rn'; try congruence.
  simpl. congruence.
- (* rn = S _ *)
  break_match; try congruence.
  destruct dbs'; try congruence.
  fancy_injr Hupd.
  destruct rn'.
  + simpl. congruence.
  + simpl. eapply IHdbs; [ | eassumption ]. congruence.
Qed.

Lemma update_record_preserves_length : forall f dbs rn dbs',
    update_record f dbs rn = Some dbs' ->
    length dbs = length dbs'.
first_induction dbs; intros0 Heq; simpl in Heq.
{ congruence. }

destruct rn.
- break_match; try congruence.
  destruct dbs'; try congruence.
  fancy_injr Heq.
  simpl. congruence.

- break_match; try congruence.
  destruct dbs'; try congruence.
  fancy_injr Heq. subst.
  simpl. f_equal. eapply IHdbs. eauto.
Qed.


(* record_match *)
Ltac trivial_witness ctor :=
    refine (ex_intro _ (ctor _) _); repeat constructor.

Lemma matching_record_config_exists : forall rs,
    exists rc, record_match rc rs.
destruct rs.
- trivial_witness RcCalc.
- trivial_witness RcCalcOut.
- trivial_witness RcFanout.
- trivial_witness RcAnalogIn.
- trivial_witness RcAnalogOut.
- trivial_witness RcBinaryIn.
- trivial_witness RcBinaryOut.
Qed.

Lemma matching_database_config_exists : forall dbs,
    exists dbc, database_match dbc dbs.
induction dbs.
{ exists []. constructor. }

destruct IHdbs as [ dbc Hdbc ].
forward eapply matching_record_config_exists as [ rc Hrc ]; eauto.
exists (rc :: dbc). constructor; eassumption.
Qed.

(* read_field *)
Lemma read_field_eq : forall rs fn fn' val,
    field_name_eq fn fn' ->
    read_field rs fn = Some val ->
    read_field rs fn' = Some val.
intros0 Heq Hread.
destruct fn; inversion Heq; subst; try assumption.
destruct_record rs as [ st ]; destruct st; unfold read_field in *;
    rewrite <- Hread; try reflexivity.
all: do 2 f_equal.
all: eapply multi_get_eq; symmetry; assumption.
Qed.

(* write_field *)
Lemma write_field_read : forall rs fn val rs',
    write_field rs fn val = Some rs' ->
    read_field rs' fn = Some val.
intros0 Heq.
destruct_record rs as [ st ]; destruct fn; try discriminate Heq.
all: destruct st, val; unfold write_field in Heq;
    compute [ unwrap_double unwrap_string unwrap_bool bind_option ] in Heq;
    try discriminate Heq.
all: match type of Heq with Some ?x = Some ?y => assert (x = y) by congruence end;
    clear Heq; subst rs'.
all: unfold read_field; do 2 f_equal; eapply multi_set_get; reflexivity.
Qed.

Lemma write_field_read_other : forall rs fn val rs' fn',
    ~ field_name_eq fn fn' ->
    write_field rs fn val = Some rs' ->
    read_field rs fn' = read_field rs' fn'.
intros0 Hne Heq.
destruct_record rs as [ st ]; destruct fn; try discriminate Heq.
all: destruct st, val; unfold write_field in Heq;
    compute [ unwrap_double unwrap_string unwrap_bool bind_option ] in Heq;
    try discriminate Heq.
all: match type of Heq with Some ?x = Some ?y => assert (x = y) by congruence end;
    clear Heq; subst rs'.
all: (destruct fn'; unfold read_field;
    match goal with | [ |- ?x = ?x ] => reflexivity | _ => idtac end).
all: try solve [ contradict Hne; constructor; reflexivity ].
all: match goal with
| [ |- Some (?Ctor ?x) = Some (?Ctor ?y) ] =>
        let Heq := fresh "Heq" in
        assert (Heq : x = y); [ | rewrite Heq; reflexivity ]
end.
all: rewrite multi_set_get_other; [ reflexivity | ].
all: contradict Hne; constructor; assumption.
Qed.

Lemma write_field_read_eq : forall rs rs' fn fn' val,
    field_name_eq fn fn' ->
    write_field rs fn val = Some rs' ->
    read_field rs' fn' = Some val.
intros. eauto using write_field_read, read_field_eq.
Qed.


(* spec_holds preservation *)

Lemma spec_holds_update_record : forall s f dbs rn dbs',
    (forall rs rs',
        named_record_state dbs rn = Some rs ->
        spec_holds_record rs rn s ->
        f rs = Some rs' ->
        spec_holds_record rs' rn s) ->
    spec_holds dbs s ->
    update_record f dbs rn = Some dbs' ->
    spec_holds dbs' s.
intros0 Hf Hspec Hupd.
forward eapply update_record_preserves_length; eauto.
unfold spec_holds in *. intros rn' rs' Hnrs'.
forward eapply named_record_state_lt; eauto.
forward eapply lt_named_record_state with (dbs := dbs) (rn := rn') as [ rs Hnrs ].
{ omega. }

destruct (eq_nat_dec rn rn').

- (* rn = rn' *)
  subst rn'.
  forward eapply update_record_lookup; eauto.

- (* rn <> rn' *)
  forward eapply update_record_lookup_other; eauto.
  replace rs' with rs by congruence. eauto.
Qed.

Lemma spec_holds_do_list : forall A s (R : A -> _ -> _ -> _ -> Prop) xs dbs dbs' oes,
    (forall x dbs dbs' oes,
        spec_holds dbs s ->
        R x dbs dbs' oes ->
        spec_holds dbs' s) ->
    spec_holds dbs s ->
    do_list R xs dbs dbs' oes -> 
    spec_holds dbs' s.
first_induction xs; intros0 HR Hspec Hdo.
{ inversion Hdo. subst. assumption. }

inversion Hdo. subst.
eapply IHxs; [ exact HR | | eassumption ].
eapply HR; [ | eassumption ].
assumption.
Qed.

Lemma spec_holds_do_indexed : forall n s (R : index n -> _ -> _ -> _ -> Prop) dbs dbs' oes,
    (forall i dbs dbs' oes,
        spec_holds dbs s ->
        R i dbs dbs' oes ->
        spec_holds dbs' s) ->
    spec_holds dbs s ->
    do_indexed R dbs dbs' oes -> 
    spec_holds dbs' s.
intros0 HR Hspec Hdo.
inversion Hdo. subst.
eapply spec_holds_do_list; [ exact HR | | eassumption ].
assumption.
Qed.

Lemma spec_holds_process_passive : forall s dbc dbs rn pp p dbs' oes,
    (pp = PP ->
        spec_holds dbs s ->
        process dbc dbs rn p dbs' oes ->
        spec_holds dbs' s) ->
    spec_holds dbs s ->
    process_passive dbc dbs rn pp p dbs' oes ->
    spec_holds dbs' s.
intros0 Hnext Hspec Hpp.
inversion Hpp; unmangle_process; subst.
- eapply Hnext; eauto.
- assumption.
Qed.

Lemma spec_holds_read_in_link : forall s dbc dbs il p dbs' oes val,
    (il_pp il = PP ->
        spec_holds dbs s ->
        process dbc dbs (il_rn il) p dbs' oes ->
        spec_holds dbs' s) ->
    spec_holds dbs s ->
    read_in_link dbc dbs il p dbs' oes val ->
    spec_holds dbs' s.
intros0 Hnext Hspec Hril.
inversion Hril. unmangle_process. subst.
eapply spec_holds_process_passive; [ | | eassumption ].
{ intros. eapply Hnext; assumption. }
assumption.
Qed.

Lemma spec_holds_write_field : forall s rs fn val rs' rn,
    spec_holds_record rs rn s ->
    denote_field_spec s rn fn val ->
    write_field rs fn val = Some rs' ->
    spec_holds_record rs' rn s.
intros0 Hspec Hfield Hwf.
unfold spec_holds_record. intros fn'; intros.
destruct (field_name_eq_dec fn fn').

- forward eapply write_field_read_eq; eauto.
  assert (VDouble f = val) by congruence.
  unfold denote_field_spec in Hfield. subst.
  erewrite spec_range_eq in Hfield by eauto.
  with spec_range hyp, fun H => rewrite H in Hfield.
  simpl in Hfield. assumption.

- forward eapply write_field_read_other; eauto.
  unfold spec_holds_record in Hspec.
  eapply Hspec; eauto.  congruence.
Qed.

Lemma spec_holds_update_input_field : forall s dbc dbs oil rn fn p dbs' oes,
    (forall il dbs p dbs' oes,
        oil = Some il ->
        il_pp il = PP ->
        spec_holds dbs s ->
        process dbc dbs (il_rn il) p dbs' oes ->
        spec_holds dbs' s) ->
    (forall il x,
        oil = Some il ->
        denote_field_spec s (il_rn il) (il_fn il) x ->
        denote_field_spec s rn fn x) ->
    spec_holds dbs s ->
    update_input_field dbc dbs oil rn fn p dbs' oes ->
    spec_holds dbs' s.
intros0 Hpp Hrange Hspec Huif.
inversion Huif; unmangle_process; subst.
{ assumption. }

propagate_spec_holds.

- eapply spec_holds_read_in_link; try eassumption.
  intros. eapply Hpp; eauto.
- eapply spec_holds_update_record; try eassumption. cbv beta.
  intros. eapply spec_holds_write_field; eauto.
Qed.

Lemma spec_holds_process_fwd_link : forall s dbc dbs fl p dbs' oes,
    (spec_holds dbs s ->
        process dbc dbs (fl_rn fl) p dbs' oes ->
        spec_holds dbs' s) ->
    spec_holds dbs s ->
    process_fwd_link dbc dbs fl p dbs' oes ->
    spec_holds dbs' s.
intros0 Hnext Hspec Hproc.
inversion Hproc; unmangle_process; subst.
eapply Hnext; eauto.
Qed.

Lemma spec_holds_process_opt_fwd_link : forall s dbc dbs ofl p dbs' oes,
    (forall fl,
        ofl = Some fl ->
        spec_holds dbs s ->
        process dbc dbs (fl_rn fl) p dbs' oes ->
        spec_holds dbs' s) ->
    spec_holds dbs s ->
    process_opt_fwd_link dbc dbs ofl p dbs' oes ->
    spec_holds dbs' s.
intros0 Hnext Hspec Hproc.
inversion Hproc; unmangle_process; subst.
- assumption.
- eapply spec_holds_process_fwd_link; try eassumption. eauto.
Qed.

Lemma spec_holds_calc_update : forall s cfg st rs' rn,
    ((forall i, denote_field_spec s rn (f_A_to_L i) (VDouble (calc_A_to_L st !!  i))) ->
        let (a2l', val') := calc_CALC cfg (calc_A_to_L st) in
        (forall i, denote_field_spec s rn (f_A_to_L i) (VDouble (a2l' !! i))) /\
        denote_field_spec s rn f_VAL (VDouble val')) ->
    spec_holds_record (RsCalc st) rn s ->
    calc_update cfg (RsCalc st) = Some rs' ->
    spec_holds_record rs' rn s.
intros0 Hcalc Hspec Hupd.
destruct_record rs' as [ st' ];
    try solve [ destruct st; simpl in Hupd; break_match; discriminate Hupd ].

spec_assert Hcalc.
{ intro i.  unfold denote_field_spec, denote_range. break_match; eauto. break_match.
  eapply Hspec; eauto. destruct st. reflexivity. }
destruct (calc_CALC _ _) as [ a2l' val' ] eqn:Heq.
unfold denote_field_spec in Hcalc.  destruct Hcalc as [ Ha2l' Hval' ].

destruct st. unfold calc_update in Hupd. unfold_field_projections.
rewrite Heq in Hupd.
fancy_injection Hupd; subst. (* for some reason fancy_injr doesn't do the right thing *)
repeat match goal with | [ H : ?x = ?x |- _ ] => clear H end.

unfold spec_holds_record. intros0 Hread Hrange.
destruct fn; try discriminate Hread.

- rewrite Hrange in Hval'. unfold denote_range in Hval'.
  unfold read_field in Hread. fancy_injr Hread. assumption.

- specialize (Ha2l' i).
  rewrite Hrange in Ha2l'. unfold denote_range in Ha2l'.
  unfold read_field in Hread.
  match type of Hread with Some (VDouble ?x) = Some (VDouble ?y) =>
        assert (x = y) by congruence end.
  subst. assumption.
Qed.

Theorem spec_holds_process_calc : forall s dbc dbs rn p dbs' oes  cfg,
    named_record_config dbc rn = Some (RcCalc cfg) ->
    (forall i il dbs p dbs' oes,
        (calc_INPA_to_INPL cfg !! i) = Some il ->
        il_pp il = PP ->
        spec_holds dbs s ->
        process dbc dbs (il_rn il) p dbs' oes ->
        spec_holds dbs' s) ->
    (forall i il x,
        (calc_INPA_to_INPL cfg !! i) = Some il ->
        denote_field_spec s (il_rn il) (il_fn il) x ->
        denote_field_spec s rn (f_A_to_L i) x) ->
    (forall fl dbs p dbs' oes,
        calc_FLNK cfg = Some fl ->
        spec_holds dbs s ->
        process dbc dbs (fl_rn fl) p dbs' oes ->
        spec_holds dbs' s) ->
    (forall st,
        (forall i, denote_field_spec s rn (f_A_to_L i) (VDouble (calc_A_to_L st !!  i))) ->
        let (a2l', val') := calc_CALC cfg (calc_A_to_L st) in
        (forall i, denote_field_spec s rn (f_A_to_L i) (VDouble (a2l' !! i))) /\
        denote_field_spec s rn f_VAL (VDouble val')) ->
    spec_holds dbs s ->
    process dbc dbs rn p dbs' oes ->
    spec_holds dbs' s.
intros0 Hnrc Hpp HA2L Hflnk Hcalc Hspec Hproc.
inversion Hproc; try congruence; unmangle_process; subst.
equate in type calc_config by congruence.

propagate_spec_holds.

- eapply spec_holds_do_indexed; eauto.  cbv beta zeta.
  intros. eapply spec_holds_update_input_field; eauto.

- eapply spec_holds_update_record; eauto.
  intros rs'; intros.

  assert (database_match dbc dbs2).
  { eapply do_indexed_preserves_match; eauto. cbv beta zeta. intros.
    eapply update_input_field_preserves_match; eauto. }

  assert (Hrm : record_match (RcCalc cfg) rs') by (eauto using named_record_match).
  inversion Hrm; subst.

  eapply spec_holds_calc_update; eauto.
  eapply Hcalc.

- eapply spec_holds_process_opt_fwd_link; [ | | eassumption ]; eauto.

Qed.

Theorem spec_holds_process_analog_in : forall s dbc dbs rn p dbs' oes  cfg,
    named_record_config dbc rn = Some (RcAnalogIn cfg) ->
    (forall fl dbs p dbs' oes,
        analog_in_FLNK cfg = Some fl ->
        spec_holds dbs s ->
        process dbc dbs (fl_rn fl) p dbs' oes ->
        spec_holds dbs' s) ->
    spec_holds dbs s ->
    process dbc dbs rn p dbs' oes ->
    spec_holds dbs' s.
intros0 Hnrc Hflnk Hspec Hproc.
inversion Hproc; try congruence; unmangle_process; subst.
equate in type analog_in_config by congruence.

propagate_spec_holds.

- eapply spec_holds_process_opt_fwd_link; [ | | eassumption ]; eauto.

Qed.


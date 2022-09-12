Require Import Arith.
Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import Sorted.
Require Import Omega.

Require Import v1.NeutronTactics.
Require Import v1.Util.
Require Import v1.Multi.
Require Import v1.ListLemmas.
Require Import v1.Wf.
Require Import v1.Terminate.
Require Import v1.Preservation.
Require Import v1.Queue.
Require Import v1.System.
Require Import v1.SystemWf.
Require v1.ExprDbl.
Require v1.ExprDblStr.

Require Import v1.EpicsTypes.
Require Import v1.EpicsRecords.
Require Import v1.Step.
Require Import v1.StepAux.

Set Default Timeout 10.
Set Implicit Arguments.


(* Misc lemmas *)

Lemma convert_value_type : forall val ty val',
    convert_value val ty = Some val' ->
    value_type val' = ty.
intros0 Heq.
destruct val; destruct ty; unfold convert_value in *;
try break_match; try discriminate.

all: repeat (break_match; try discriminate).
all: try solve [fancy_injr <- Heq; subst; reflexivity].
Qed.


Definition interp_update_record f : forall dbs rn,
    forall rs rs',
    lookup_state dbs rn = Some rs ->
    f rs = Some rs' ->
    { dbs' | update_record f dbs rn = Some dbs' }.
first_induction dbs; destruct rn; simpl in *; intros0 Hrs Hf.
- congruence.
- congruence.
- fancy_injr Hrs. rewrite Hf.
  eexists. reflexivity.
- forward eapply IHdbs as [ dbs' Hdbs' ]; eauto.  rewrite Hdbs'.
  eexists. reflexivity.
Defined.


Definition interp_write_field rs fn val :
    forall rt,
    record_state_type rs = rt ->
    record_has_field rt fn (value_type val) ->
    { rs' | write_field rs fn val = Some rs' }.
intros0 Hrst Hrhf.
destruct (write_field _ _ _) eqn:Heq.
{ eexists. reflexivity. }

exfalso.
invc Hrhf;
destruct_record rs as [ st ]; try discriminate;
destruct val; try discriminate.

all: destruct st; unfold write_field in Heq.

(* TEnum stuff *)
all: try (
    unfold unwrap_enum in Heq;
    on (TEnum _ = _), (fun H => simpl in H; fancy_injection H);
    break_match; try congruence
); try discriminate Heq.

all: try (
    unfold unwrap_array in Heq;
    try on (RtArrayCalcOut _ = _), (fun H => simpl in H; fancy_injection H);
    try on (RtWaveform _ _ = _), (fun H => simpl in H; fancy_injection H);
    try on (RtSubarray _ _ _ = _), (fun H => simpl in H; fancy_injection H);
    on (TArray _ _ = _), (fun H => simpl in H; fancy_injection H);
    break_match; [ break_match | ]; [ unfold bind_option in Heq | |]; try congruence
); try discriminate Heq.

Defined.

Definition interp_write_record_field dbs rn fn val :
    forall dbt,
    database_state_type dbs = dbt ->
    wfm_field_access dbt rn fn (value_type val) ->
    { dbs' | write_record_field dbs rn fn val = Some dbs' }.
intros0 Hdbt Hwf.
destruct (write_record_field _ _ _ _) eqn:Heq.
{ eexists. reflexivity. }

exfalso.

invc Hwf.

forward eapply lookup_length_ex with (ys := dbs) as [ rs Hrs ]; eauto using map_length.
forward eapply lookup_state_type_eq; try eassumption; eauto.
forward eapply (@interp_write_field rs fn val) as [ rs' Hrs' ]; eauto.
{ congruence. }

unfold write_record_field in Heq.
forward eapply interp_update_record as [ dbs' Hdbs' ];
[ | | rewrite Hdbs' in Heq; discriminate Heq ]; eauto.
Defined.

Ltac do_write_record_field pf :=
    match type of pf with
    | forall dbs', write_record_field ?dbs ?rn ?fn ?val = Some dbs' -> _ =>
            let dbs' := fresh "dbs'" in
            let Hdbs' := fresh "H" dbs' in
            forward eapply (@interp_write_record_field dbs rn fn val) as [ dbs' Hdbs' ];
            [ (* db type *) eassumption
            | (* wfm *) idtac
            | specialize (pf dbs' Hdbs') ]
    end.


Definition interp_read_field rs fn :
    forall rt ty,
    record_state_type rs = rt ->
    record_has_field rt fn ty ->
    { val | read_field rs fn = Some val /\
            value_type val = ty }.
intros0 Hrt Hrhf.
destruct (read_field _ _) eqn:Heq.

- eexists. split; [ reflexivity | ].
  invc Hrhf;
  destruct_record rs as [ st ]; try discriminate;
  destruct st; unfold read_field in Heq;
  fancy_injr <- Heq; try constructor.

  (* TArray stuff *)
  all: try (on (RtArrayCalcOut _ = _), invc; reflexivity).
  all: try (on (RtWaveform _ _ = _), invc; reflexivity).
  all: try (on (RtSubarray _ _ _ = _), invc; reflexivity).

- exfalso.
  invc Hrhf;
  destruct_record rs as [ st ]; try discriminate;
  destruct st; unfold read_field in Heq;
  discriminate Heq.
Defined.

Definition interp_read_record_field dbs rn fn :
    forall dbt ty,
    database_state_type dbs = dbt ->
    wfm_field_access dbt rn fn ty ->
    { val | read_record_field dbs rn fn = Some val /\
            value_type val = ty }.
intros0 Hdbt Hwf.

destruct (lookup_state dbs rn) as [ rs | ] eqn:Hrs; cycle 1.
{ exfalso. invc Hwf.
  forward eapply lookup_length_ex with (ys := dbs); eauto using map_length.
  firstorder congruence. }
remember (record_state_type rs) as rt.
forward eapply lookup_state_type; eauto.
forward eapply (@interp_read_field rs fn) with (rt := rt) (ty := ty) as [ val Hval ].
{ eauto. }
{ invc Hwf. congruence. }
destruct Hval as [Hval Hty].

exists val. split.
- unfold read_record_field.
  rewrite Hrs. unfold bind_option. assumption.
- assumption.
Defined.

Ltac do_read_record_field pf :=
    match type of pf with
    | forall val,
      read_record_field ?dbs ?rn ?fn = Some val -> 
      value_type val = ?ty -> _ =>
            let val := fresh "val" in
            let Hval := fresh "H" val in
            let Heqty := fresh "Heq" ty in
            forward eapply (@interp_read_record_field dbs rn fn) as [ val Hval ];
            [ (* db type *)eassumption
            | (* wfm *) idtac
            | destruct Hval as [Hval Heqty];
              specialize (pf val Hval Heqty) ]
    end.

Definition interp_run_calculate_record expr fn_out rs :
    forall rt,
    record_state_type rs = rt ->
    wfm_calculate rt fn_out ->
    { rs' | run_calculate_record expr fn_out rs = Some rs' }.
intros0 Hrt Hwf.

destruct (run_calculate_record expr fn_out rs) eqn:Heq.
{ eexists. reflexivity. }

exfalso.
destruct Hwf as [ ? ? Hty Hfn Hf_in Hf_out ].
unfold run_calculate_record in Heq.
repeat on (_ = (_ : record_type) \/ _), destruct_;
destruct_record rs as [ st ]; simpl in Hrt; try congruence;
symmetry in Hrt; subst rt.

- (* Calc *)
  destruct st. break_match.
  destruct Hfn; subst fn_out; try solve [ inversion Hf_out ].
  + (* VAL *) discriminate.

- (* CalcOut *)
  destruct st. break_match.
  destruct Hfn; subst fn_out; try solve [ inversion Hf_out ].
  + (* VAL *) discriminate.
  + (* OVAL *) discriminate.
Defined.

Definition interp_run_calculate expr fn_out dbs rn :
    forall dbt rt,
    database_state_type dbs = dbt ->
    lookup dbt rn = Some rt ->
    wfm_calculate rt fn_out ->
    { dbs' | run_calculate expr fn_out dbs rn = Some dbs' }.
intros0 Hdbt Hrt Hwf.
destruct (run_calculate expr fn_out dbs rn) eqn:Heq.
{ eexists. reflexivity. }

exfalso.

subst dbt.
forward eapply lookup_length_ex with (ys := dbs) as [ rs Hrs ]; eauto using map_length.
forward eapply lookup_state_type_eq; try eassumption; eauto.
subst rt.
forward eapply (@interp_run_calculate_record expr fn_out rs) as [ rs' Hrs' ]; eauto.

unfold run_calculate in Heq.
forward eapply interp_update_record as [ dbs' Hdbs' ];
[ | | rewrite Hdbs' in Heq; discriminate Heq ]; eauto.
Defined.

Ltac do_run_calculate pf :=
    match type of pf with
    | forall dbs', run_calculate ?expr ?fn_out ?dbs ?rn = Some dbs' -> _ =>
            let dbs' := fresh "dbs'" in
            let Hdbs' := fresh "H" dbs' in
            forward eapply (@interp_run_calculate expr fn_out dbs rn) as [ dbs' Hdbs' ];
            [ (* db type *) eassumption
            | (* record type *) eassumption
            | (* wfm *) idtac
            | specialize (pf dbs' Hdbs') ]
    end.

Definition interp_run_calculate_str_record expr fn_out_dbl fn_out_str rs :
    forall rt,
    record_state_type rs = rt ->
    wfm_calculate_str rt fn_out_dbl fn_out_str ->
    { rs' | run_calculate_str_record expr fn_out_dbl fn_out_str rs = Some rs' }.
intros0 Hrt Hwf.

destruct (run_calculate_str_record expr fn_out_dbl fn_out_str rs) eqn:Heq.
{ eexists. reflexivity. }

exfalso.
destruct Hwf.
unfold run_calculate_str_record in Heq.
destruct_record rs as [ st ]; simpl in Hrt; try congruence;
symmetry in Hrt; subst rt.

break_match.

- forward eapply interp_write_field as [ rs' Hrs' ]; cycle 2.
  + rewrite Heq in Hrs'. discriminate.
  + reflexivity.
  + eauto.

- forward eapply interp_write_field as [ rs' Hrs' ]; cycle 2.
  + rewrite Heq in Hrs'. discriminate.
  + reflexivity.
  + eauto.
Defined.

Definition interp_run_calculate_str expr fn_out_dbl fn_out_str dbs rn :
    forall dbt rt,
    database_state_type dbs = dbt ->
    lookup dbt rn = Some rt ->
    wfm_calculate_str rt fn_out_dbl fn_out_str ->
    { dbs' | run_calculate_str expr fn_out_dbl fn_out_str dbs rn = Some dbs' }.
intros0 Hdbt Hrt Hwf.
destruct (run_calculate_str expr fn_out_dbl fn_out_str dbs rn) eqn:Heq.
{ eexists. reflexivity. }

exfalso.

subst dbt.
forward eapply lookup_length_ex with (ys := dbs) as [ rs Hrs ]; eauto using map_length.
forward eapply lookup_state_type_eq; try eassumption; eauto.
subst rt.
forward eapply (@interp_run_calculate_str_record expr fn_out_dbl fn_out_str rs)
    as [ rs' Hrs' ]; eauto.

unfold run_calculate_str in Heq.
forward eapply interp_update_record as [ dbs' Hdbs' ];
[ | | rewrite Hdbs' in Heq; discriminate Heq ]; eauto.
Defined.

Ltac do_run_calculate_str pf :=
    match type of pf with
    | forall dbs', run_calculate_str ?expr ?fn_out_dbl ?fn_out_str ?dbs ?rn = Some dbs' -> _ =>
            let dbs' := fresh "dbs'" in
            let Hdbs' := fresh "H" dbs' in
            forward eapply (@interp_run_calculate_str expr fn_out_dbl fn_out_str dbs rn)
                as [ dbs' Hdbs' ];
            [ (* db type *) eassumption
            | (* record type *) eassumption
            | (* wfm *) idtac
            | specialize (pf dbs' Hdbs') ]
    end.


Axiom arbitrary_type : unit -> field_type.
Axiom arbitrary_double : unit -> e_double.
Axiom arbitrary_string : unit -> e_string.
Axiom arbitrary_bool : unit -> bool.
Axiom arbitrary_enum : forall max, e_enum max.
Axiom arbitrary_long : unit -> e_long.
Axiom arbitrary_array : forall elem size, e_array elem size.

Definition arbitrary_typed_value (ty : field_type) : value :=
    match ty with
    | TDouble => VDouble (arbitrary_double tt)
    | TString => VString (arbitrary_string tt)
    | TEnum max => VEnum (arbitrary_enum max)
    | TLong => VLong (arbitrary_long tt)
    | TArray elem size => VArray (arbitrary_array elem size)
    end.

Definition arbitrary_value : unit -> value :=
    fun u => arbitrary_typed_value (arbitrary_type u).

Definition arbitrary_havoc_state : unit -> havoc_state.
(* TODO: this version results in a non-pure havoc_fields function *)
intros. constructor. intros. exact (arbitrary_value tt).
Defined.

Lemma arbitrary_typed_value_ty : forall ty,
    value_type (arbitrary_typed_value ty) = ty.
intros. destruct ty; reflexivity.
Qed.


Definition interp_convert_value val ty :
    value_convertible (value_type val) ty ->
    { val' | convert_value val ty = Some val' }.
intros0 Hconv.
destruct (convert_value val ty) as [ val' | ] eqn:?.
{ exists val'. reflexivity. }

exfalso.
destruct val; simpl in *; invc Hconv; try discriminate.
- (* enum *) break_match. break_match; try omega. discriminate.
- (* long *) break_match. discriminate.
- (* array *) break_match; try congruence. break_match; try congruence.
Defined.

Ltac do_convert_value pf :=
    match type of pf with
    | forall val', convert_value ?val ?ty = Some val' -> _ =>
            let val' := fresh "val'" in
            let Hval' := fresh "H" val' in
            forward eapply (@interp_convert_value val ty) as [ val' Hval' ];
            [ (* convertible *) idtac
            | specialize (pf val' Hval') ]
    end.

Ltac do_denote_expr_dbl pf :=
    match type of pf with
    | forall f, ExprDbl.denote ?expr = Some f -> _ =>
            let f := fresh "f" in
            let Hf := fresh "H" f in
            let HH := fresh "HH" in
            assert (exists f, ExprDbl.denote expr = Some f) as HH;
            [ (* Hwf *) idtac
            | destruct (ExprDbl.denote expr) as [f | ] eqn:Hf;
              [ specialize (pf f eq_refl)
              | exfalso; destruct HH; congruence ]
            ]
    end.

Ltac do_denote_expr_dbl_str pf :=
    match type of pf with
    | forall f, ExprDblStr.denote ?expr = Some f -> _ =>
            let f := fresh "f" in
            let Hf := fresh "H" f in
            forward eapply (@ExprDblStr.denote_total _ expr) as [ f Hf ];
            [ (* Hwf *) idtac
            | specialize (pf f Hf) ]
    end.

Ltac do_lookup pf :=
    match type of pf with
    | forall r, lookup ?db ?rn = Some r -> _ =>
            let r := fresh "r" in
            let Hr := fresh "H" r in
            destruct (lookup db rn) as [ r | ] eqn:Hr; cycle 1;
            [ (* None *) exfalso; clear pf
            | specialize (pf r eq_refl) ]
    end.

Ltac do_set_record_state pf :=
    match type of pf with
    | forall dbs', update_record ?f ?dbs ?rn = Some dbs' -> _ =>
            let dbs' := fresh "dbs'" in
            let Hdbs' := fresh "H" dbs' in
            forward eapply (@interp_update_record f dbs rn) as [ dbs' Hdbs' ];
            [ (* lookup ok *) eauto
            | (* `f rs` ok *) eauto
            | specialize (pf dbs' Hdbs') ]
    end.



Definition interp_db_step rn op dbs :
    forall dbt rt,
    database_state_type dbs = dbt ->
    lookup_type dbt rn = Some rt ->
    wfm_instr dbt rt op ->
    is_db_op op = true ->
    { dbs' | db_step rn op dbs dbs' }.
intros0 Hdbt Hrt Hwf Hdb_op.
destruct op; (inversion Hdb_op || clear Hdb_op).

- pose proof (@SSetConst rn fn val dbs) as pf.
  do_write_record_field pf.
    { (* wfm *) inversion Hwf. econstructor; eauto. }
  eexists. eassumption.

- pose proof (@SCopy rn fn_src src_ty fn_dest dest_ty dbs) as pf.
  do_read_record_field pf.
    { (* wfm *) inversion Hwf. econstructor; eauto. }
  do_convert_value pf.
    { (* conv *) inversion Hwf. congruence. }
  do_write_record_field pf.
    { (* wfm *) inversion Hwf. econstructor; eauto.
      replace (value_type _) with dest_ty by (symmetry; eauto using convert_value_type).
      assumption. }
  eexists. eassumption.

- pose proof (@SReadLink rn il il_ty fn f_ty dbs) as pf.
  do_read_record_field pf.
    { (* wfm *) invc Hwf. on >wfm_field_link, invc. eauto. }
  do_convert_value pf.
    { (* conv *) invc Hwf. assumption. }
  do_write_record_field pf.
    { (* wfm *) invc Hwf. on >wfm_field_link, invc.
      replace (value_type _) with f_ty by (symmetry; eauto using convert_value_type).
      econstructor; eauto. }
  eexists. eassumption.

- pose proof (@SWriteLink rn fn f_ty ol ol_ty dbs) as pf.
  do_read_record_field pf.
    { (* wfm *) invc Hwf. econstructor; eauto. }
  do_convert_value pf.
    { (* conv *) invc Hwf. assumption. }
  do_write_record_field pf.
    { (* wfm *) invc Hwf. on >wfm_field_link, invc.
      replace (value_type _) with ol_ty by (symmetry; eauto using convert_value_type).
      assumption. }
  eexists. eassumption.

- pose proof (@SCalculate rn expr fn_out dbs) as pf.
  do_denote_expr_dbl pf.
    { invc Hwf. assumption. }
  do_run_calculate pf; [eauto.. | ].
    { invc Hwf. assumption. }
  eexists. eassumption.

- pose proof (@SCalculateStr rn expr fn_out_dbl fn_out_str dbs) as pf.
  do_denote_expr_dbl_str pf.
    { invc Hwf. assumption. }
  cbv zeta in pf.
  do_run_calculate_str pf; [eauto.. | ].
    { invc Hwf. assumption. }
  eexists. eassumption.

- (* this makes SHavocUpdate a no-op *)
  destruct (lookup dbs rn) as [rs' | ] eqn:Hrs; cycle 1.
    { forward eapply lookup_length_ex with (ys := dbs) as HH;
          try solve [subst dbt; eauto using map_length].
      exfalso. destruct HH. congruence. }

  pose proof (@SHavocUpdate rn dbs rs') as pf.
  do_lookup pf.
    { discriminate. }
  spec pf by congruence.
  do_set_record_state pf.
  eexists. eassumption.

- pose proof (@SHavocWrite rn ol ol_ty dbs (arbitrary_typed_value ol_ty)) as pf.
  spec pf by eapply arbitrary_typed_value_ty.
  do_write_record_field pf.
    { (* wfm *) invc Hwf. on >wfm_field_link, invc.
      rewrite arbitrary_typed_value_ty. assumption. }
  eexists. eassumption.

Defined.

Definition interp_output_step rn op dbs :
    forall dbt rt,
    database_state_type dbs = dbt ->
    lookup_type dbt rn = Some rt ->
    wfm_instr dbt rt op ->
    is_output_op op = true ->
    { out | output_step rn op dbs out }.
intros0 Hdbt Hrt Hwf Hout_op.
destruct op; (inversion Hout_op || clear Hout_op).

- pose proof (@SHwWrite rn fn f_ty out_ty dbs) as pf.
  do_read_record_field pf.
    { (* wfm *) invc Hwf. econstructor; eauto. }
  do_convert_value pf.
    { (* conv *) invc Hwf. assumption. }
  eexists. eassumption.

- pose proof (@SScheduleCallback rn delay code dbs) as pf.
  eexists. eassumption.

Defined.


Definition interp_step dbp ss :
    let dbt := database_program_type dbp in
    database_state_type (state_dbs ss) = dbt ->
    state_stk ss <> [] ->
    wfm_state dbt ss ->
    { ss', oes | step dbp ss ss' oes }.
intros0 Hty Hstk Hwf.

destruct ss as [ dbs stk ]. unfold state_dbs, state_stk in *.
destruct stk as [ | fr rest ]; try congruence. clear Hstk.
assert (Hwf_fr : wfm_frame dbt fr) by (invc Hwf; eauto).
destruct fr as [ rn code ]. unfold frame_rn, frame_code in *.
destruct code as [ | op ops ].

{
  pose proof (@SPop dbp dbs rn rest) as pf.
  do_lookup pf.
    { invc Hwf_fr. rewrite <- Hty in *.
      forward eapply lookup_length_ex with (ys := dbs); eauto using map_length.
      simpl in *. break_exists. congruence. }
  eexists. exact pf.
}

destruct (lookup_type dbt rn) as [ rt | ] eqn:Hrt; cycle 1.
{ exfalso. invc Hwf. on (wfm_frame _ _), invc. simpl in *. congruence. }
assert (Hwf_op : wfm_instr dbt rt op).
{ invc Hwf_fr. on (Forall (wfm_instr _ _) _), invc. subst. simpl in *. congruence. }

destruct (is_db_op op) eqn:Hdbop.
2: destruct (is_output_op op) eqn:Hoop.
3: destruct op; try discriminate Hdbop; try discriminate Hoop.

- (* SDb *)
  pose proof (@SDb dbp dbs rn op ops rest) as pf.
  forward eapply (@interp_db_step rn op dbs) as [ dbs' Hdbs' ]; [ eauto.. | ].
  specialize (pf dbs' Hdbs').
  eexists. exact pf.

- (* SOutput *)
  pose proof (@SOutput dbp dbs rn op ops rest) as pf.
  forward eapply (@interp_output_step rn op dbs) as [ dbs' Hdbs' ]; [ eauto.. | ].
  specialize (pf dbs' Hdbs').
  eexists. exact pf.

- (* SProcess *)
  pose proof (@SProcess dbp dbs rn fl ops rest) as pf.
  do_lookup pf.
  { invc Hwf_op. on >wfm_record_link, invc.
    forward eapply lookup_length_ex with (ys := dbp); eauto using map_length.
    firstorder congruence. }
  do_lookup pf.
    { invc Hwf_fr. rewrite <- Hty in *.
      forward eapply lookup_length_ex with (ys := dbs); eauto using map_length.
      simpl in *. break_exists. congruence. }
  eexists. exact pf.

- (* SCalcCondNo / SCalcCondYes *)
  (* A little tricky because we need to advance several steps before we know
     whether we want the No or Yes variant. *)
  set_inversion Hwf_op.
  forward eapply (@interp_read_record_field dbs rn fn_cur) as HH; eauto.
    { (* wfm *) econstructor; eassumption. }
    destruct HH as [ cur_val [ Hcur_rrf Hcur_ty ] ].
  destruct cur_val; try discriminate Hcur_ty. rename e into cur.
  forward eapply (@interp_read_record_field dbs rn fn_prev) as HH; eauto.
    { (* wfm *) econstructor; eassumption. }
    destruct HH as [ prev_val [ Hprev_rrf Hprev_ty ] ].
  destruct prev_val; try discriminate Hprev_ty. rename e into prev.
  destruct (eval_calc_cond cur prev oopt) eqn:Heval.

  + (* Yes *)
    pose proof (@SCalcCondYes dbp dbs rn fn_cur fn_prev oopt body ops rest) as pf.
    spec_evar pf. specialize (pf Hcur_rrf).
    spec_evar pf. spec pf by reflexivity.
    spec_evar pf. specialize (pf Hprev_rrf).
    spec_evar pf. spec pf by reflexivity.
    spec pf by assumption.
    eexists. eassumption.

  + (* No *)
    pose proof (@SCalcCondNo dbp dbs rn fn_cur fn_prev oopt body ops rest) as pf.
    spec_evar pf. specialize (pf Hcur_rrf).
    spec_evar pf. spec pf by reflexivity.
    spec_evar pf. specialize (pf Hprev_rrf).
    spec_evar pf. spec pf by reflexivity.
    spec pf by assumption.
    eexists. eassumption.

- (* SCheckPACTZero / SCheckPACTNonZero *)
  set_inversion Hwf_op.
  forward eapply (@interp_read_record_field dbs rn f_PACT) as HH; eauto.
    { (* wfm *) econstructor; eassumption. }
    destruct HH as ( pact & Hrrf & Hpact_ty ).
  forward eapply (value_eq_dec pact _) as HH.
    destruct HH.

  + (* Zero *)
    pose proof (@SCheckPACTZero dbp dbs rn ops rest) as pf.
    spec_evar pf. specialize (pf Hrrf).
    spec pf by eassumption.
    eexists. eassumption.

  + (* NonZero *)
    pose proof (@SCheckPACTNonZero dbp dbs rn ops rest) as pf.
    spec_evar pf. specialize (pf Hrrf).
    spec pf by eassumption.
    eexists. eassumption.

- (* SHavocProcessNo / SHavocProcessYes *)
  destruct (arbitrary_bool tt).

  + (* No *) 
    pose proof (@SHavocProcessNo dbp dbs rn fl ops rest) as pf.
    eexists. eassumption.

  + pose proof (@SHavocProcessYes dbp dbs rn fl ops rest) as pf.
    destruct (lookup_program dbp (rl_rn fl)) as [ rp | ] eqn:Hrp; cycle 1.
    { exfalso. invc Hwf_op. on >wfm_record_link, invc.
      forward eapply lookup_length_ex with (ys := dbp); eauto using map_length.
      firstorder congruence. }
    specialize (pf rp eq_refl).
    eexists. exact pf.

Defined.

Definition interp_star_step dbp dbm ss :
    let dbt := database_program_type dbp in
    database_time dbm dbp ->
    database_state_type (state_dbs ss) = dbt ->
    wfm_database dbt dbp ->
    wfm_state dbt ss ->
    { ss', oes | star_step dbp ss ss' oes /\ state_stk ss' = [] }.
intros0 Htime.
induction ss using (well_founded_induction (state_lt_well_founded dbm)).
rename H into IH.
intros0 Hty Hwfdb Hwfs.

destruct ss as [ dbs stk ] eqn:Heqss. unfold state_dbs, state_stk in *.
destruct stk eqn:Heqstk.

{ exists ss []. subst ss. split; constructor. }

forward eapply interp_step as [ ss' oes' Hss' ]; eauto.
{ eassumption. }
{ simpl. discriminate. }

forward eapply (IH ss') as [ ss'' oes'' Hss'' ];
  eauto using step_decreasing, step_preserves_wfm_state.
{ fold (state_dbs ss').
  erewrite <- step_preserves_state_type; eauto. eassumption. }
{ eapply step_preserves_wfm_state; eauto. reflexivity. }
destruct Hss'' as [Hss'' Hnil].

exists ss'' (oes' ++ oes''). split.
- econstructor; eassumption.
- assumption.
Defined.

Definition interp_start_handle dbp ie :
    let dbt := database_program_type dbp in
    wfm_input_event dbt ie ->
    { stk | start_handle dbp ie stk }.
intros0 Hwfie; destruct ie.

- (* ShProcess *)
  destruct (lookup_program dbp rn) as [ rp | ] eqn:Hrp; cycle 1.
  { exfalso. invc Hwfie.
    forward eapply lookup_length_ex with (ys := dbp); eauto.
    { eapply map_length. }
    firstorder congruence. }
  eexists. econstructor; eauto.

- (* ShRunCallback *)
  eexists. econstructor; eauto.
Defined.

Definition interp_handle dbp dbm dbs ie :
    let dbt := database_program_type dbp in
    database_time dbm dbp ->
    database_state_type dbs = dbt ->
    wfm_database dbt dbp ->
    wfm_input_event dbt ie ->
    { dbs', oes | handle dbp dbs ie dbs' oes }.
intros0 Htime Hsty Hwf Hwfie.

forward eapply (@interp_start_handle dbp ie) as [ fr Hfr ]; eauto.
destruct (lookup dbs (frame_rn fr)) eqn:?; cycle 1.
  {
    exfalso.

    subst. eapply f_equal with (f := @length _) in Hsty.
    unfold database_state_type, database_program_type in Hsty.
    do 2 erewrite map_length in Hsty.

    invc Hfr; invc Hwfie.
    - forward eapply lookup_length_ex with (xs := dbp) (ys := dbs); eauto.
      simpl in *. break_exists. congruence.
    - forward eapply lookup_length_ex with (ys := dbs); eauto.
        { unfold database_program_type. rewrite map_length. eauto. }
      simpl in *. break_exists. congruence.
  }
forward eapply (@interp_star_step dbp dbm (State dbs [fr])) as [ ss' oes Hstep ]; eauto.
  { (* wfm_state *) constructor; eauto using start_handle_preserves_wfm. }

eexists (state_dbs ss') (_ :: _ :: oes).
destruct Hstep as [ Hstep Hstk ].
econstructor; eauto.
  { destruct ss'; simpl in *. congruence. }
Defined.


Definition interp_insert_one_evt_sorted : forall (evt : timestamped_event) evts,
    { evts' | insert_one evt evts evts' /\
        (StronglySorted te_le evts -> StronglySorted te_le evts')}.
first_induction evts; intros.
{ (* empty list *) exists [evt]. split.
  - constructor.
  - intros. constructor; eauto. }

rename a into evt0.
(* Keep going until we find an event that is strictly greater than `evt`.  This
   ensures that inserting several events with the same timestamp will preserve
   their relative ordering. *)
destruct (Z_le_dec (te_when evt0) (te_when evt)).

- (* insert later *)
  destruct (IHevts evt) as [evts' Hevts']. break_and.
  exists (evt0 :: evts'). split.
  + constructor; assumption.
  + inversion 1. subst. constructor; eauto.
    rewrite Forall_forall in *. intros evt' Hin.
    forward eapply insert_one_from as HH; eauto. destruct HH; eauto.
    unfold te_le. subst. eauto.

- (* insert now *)
  exists (evt :: evt0 :: evts). split.
  + constructor; assumption.
  + inversion 1. constructor; eauto.
    rewrite Forall_forall in *. intros.
    on >In, fun H => destruct H as [ ? | Hin ]; subst; unfold te_le in *; eauto.
    { omega. }
    { on _, fun H => forward eapply (H _ Hin). omega. }
Defined.

Definition interp_insert_many_evts_sorted : forall (new : list timestamped_event) evts,
    { evts' | insert_many new evts evts' /\
        (StronglySorted te_le evts -> StronglySorted te_le evts')}.
first_induction new; intros.
{ (* empty `new` *) exists evts. split; [ constructor | eauto ]. }

rename a into evt, new into rest.
destruct (interp_insert_one_evt_sorted evt evts) as (evts' & ? & ?).
destruct (IHnew evts') as (evts'' & ? & ?).
exists evts''. split; eauto.
econstructor; eassumption.
Defined.

Definition interp_system_step : forall now sys,
    system_state_wf sys ->
    { sys', oes | system_step now sys sys' oes} +
            ~(exists evt, In evt (sys_evts sys) /\ te_when evt <= now).
intros0 Hwf. destruct sys.

destruct sys_evts as [ | evt evts ] eqn:?.
{ (* no events *) right. intro. break_exists. simpl in *. firstorder. }

forward eapply (@interp_handle sys_dbp sys_dbm sys_dbs (te_evt evt)) as [ dbs' oes Hstep ];
    try invc Hwf; simpl in *; eauto; try congruence.
  { (* evt wf *) rewrite Forall_forall in *. on _, fun H => rewrite H.
    eapply swf_evts_wfm. simpl. eauto. }
forward eapply (@interp_insert_many_evts_sorted (conv_callbacks oes now) evts) as [evts' Hevts'];
    eauto. break_and.

left. eexists. econstructor; invc Hwf; simpl in *; eauto.
  { (* sorted *) invc swf_evts_sorted. eauto. }
Defined.

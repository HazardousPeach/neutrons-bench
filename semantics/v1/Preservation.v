Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Omega.

Require Import v1.NeutronTactics.
Require Import v1.Multi.
Require Import v1.Util.
Require Import v1.EpicsTypes.
Require Import v1.EpicsRecords.
Require Import v1.Step.
Require Import v1.ListLemmas.
Require Import v1.Wf.
Require Import v1.System.
Require Import v1.Queue.
Require Import v1.SystemWf.

(* Preservation of x_state_type *)

Lemma write_field_preserves_state_type : forall rs fn val rs',
    write_field rs fn val = Some rs' ->
    record_state_type rs = record_state_type rs'.
intros0 Hwf. destruct_record rs as [ st ];
destruct fn; try destruct n; try discriminate Hwf;
unfold write_field in Hwf; destruct st;
destruct val; try discriminate Hwf;
unfold
    unwrap_double, unwrap_string, unwrap_enum,
    bind_option in Hwf;
repeat (break_match; try discriminate);
fancy_injection Hwf; clear Hwf; subst rs';
unfold record_state_type;
reflexivity.
Qed.

Lemma update_record_preserves_state_type : forall f dbs rn dbs',
    (forall rs rs',
        lookup_state dbs rn = Some rs ->
        lookup_state dbs' rn = Some rs' ->
        f rs = Some rs' ->
        record_state_type rs = record_state_type rs') ->
    update_record f dbs rn = Some dbs' ->
    database_state_type dbs = database_state_type dbs'.
first_induction rn; intros0 Hf Hup;
destruct dbs; destruct dbs'; simpl in *; try break_match; try congruence.
- invc Hup. specialize (Hf ?? ?? *** *** **). congruence.
- invc Hup. erewrite IHrn by eauto. reflexivity.
Qed.

Lemma write_record_field_preserves_state_type : forall dbs rn fn val dbs',
    write_record_field dbs rn fn val = Some dbs' ->
    database_state_type dbs = database_state_type dbs'.
intros0 Hwrf. unfold write_record_field in Hwrf.
eapply update_record_preserves_state_type; eauto.
cbv beta. eauto using write_field_preserves_state_type.
Qed.

Lemma run_calculate_record_preserves_state_type : forall f fn_out rs rs',
    run_calculate_record f fn_out rs = Some rs' ->
    record_state_type rs = record_state_type rs'.
intros0 Hcalc.
destruct_record rs as [st]; try discriminate Hcalc; destruct st.
all: simpl in Hcalc; do 2 break_match; try discriminate Hcalc.
all: injection Hcalc; intro; subst.
all: simpl.
all: reflexivity.
Qed.

Lemma run_calculate_preserves_state_type : forall expr fn_out dbs rn dbs',
    run_calculate expr fn_out dbs rn = Some dbs' ->
    database_state_type dbs = database_state_type dbs'.
intros0 Hcalc. unfold run_calculate in Hcalc.
eapply update_record_preserves_state_type;
  eauto using run_calculate_record_preserves_state_type.
Qed.

Lemma run_calculate_str_preserves_state_type : forall expr fn_out_dbl fn_out_str dbs rn dbs',
    run_calculate_str expr fn_out_dbl fn_out_str dbs rn = Some dbs' ->
    database_state_type dbs = database_state_type dbs'.
intros0 Hcalc. unfold run_calculate_str in Hcalc.
eapply update_record_preserves_state_type; eauto.
intros0 Hrs Hrs' Heq. unfold run_calculate_str_record in Heq.
destruct_record rs as [ st ]; try discriminate Heq.
break_match; eapply write_field_preserves_state_type; eauto.
Qed.

Lemma db_step_preserves_state_type : forall rn op dbs dbs',
    db_step rn op dbs dbs' ->
    database_state_type dbs = database_state_type dbs'.
intros0 Hstep.
invc Hstep.

- (* MSetConst *) eauto using write_record_field_preserves_state_type.
- (* MCopy *) eauto using write_record_field_preserves_state_type.
- (* MReadLink *) eauto using write_record_field_preserves_state_type.
- (* MWriteLink *) eauto using write_record_field_preserves_state_type.
- (* MCalculate *) eauto using run_calculate_preserves_state_type.
- (* MCalculateStr *) eauto using run_calculate_str_preserves_state_type.
- (* MHavocUpdate *)
  eapply update_record_preserves_state_type; eauto.
  cbv beta. intros0 Hrs Hrs' Heq. invc Heq.
  congruence.
- (* MHavocWrite *) eauto using write_record_field_preserves_state_type.
Qed.

Lemma step_preserves_state_type : forall dbp ss ss' oes,
    step dbp ss ss' oes ->
    database_state_type (state_dbs ss) = database_state_type (state_dbs ss').
intros0 Hstep.
invc Hstep; try reflexivity.

- (* db step *)
  simpl. eauto using db_step_preserves_state_type.
Qed.

Lemma star_step_preserves_state_type : forall dbp ss ss' oes,
    star_step dbp ss ss' oes ->
    database_state_type (state_dbs ss) = database_state_type (state_dbs ss').
induction 1.

- reflexivity.
- erewrite step_preserves_state_type by eassumption.
  eassumption.
Qed.

Theorem handle_preserves_state_type : forall dbp dbs ie dbs' oes,
    handle dbp dbs ie dbs' oes ->
    database_state_type dbs = database_state_type dbs'.
intros0 Hh.
invcs Hh.
forward eapply star_step_preserves_state_type; eauto.
Qed.


(* preservation of wfm_x *)

Lemma lookup_preserves_wfm : forall dbt dbp rn rp,
    lookup_program dbp rn = Some rp ->
    wfm_database dbt dbp ->
    wfm_record dbt rp.
first_induction rn; intros0 Hlp Hwf.

- destruct dbp as [| rp0 dbp ]; simpl in *; try congruence.
  fancy_injr Hlp. invcs Hwf. assumption.

- destruct dbp as [| rp0 dbp ]; simpl in *; try congruence.
  invcs Hwf. eapply IHrn; eauto.
Qed.

Theorem step_preserves_wfm_state : forall dbp dbt state state' oes,
    dbt = database_program_type dbp ->
    wfm_database dbt dbp ->
    step dbp state state' oes ->
    wfm_state dbt state ->
    wfm_state dbt state'.
intros0 Hdpt Hdb Hstep Hwf.
invcs Hstep; invcs Hwf.

- (* SDb *)
  econstructor; eauto.
  on >wfm_frame, invcs.
  econstructor; eauto.

- (* SOutput *)
  econstructor; eauto.
  on >wfm_frame, invcs.
  econstructor; eauto.

- (* SPop *)
  unfold wfm_state. assumption.

- (* SProcess *)
  econstructor; [| econstructor ]; eauto.
  + forward eapply lookup_preserves_wfm as Hwfr; eauto.
    unfold wfm_record in Hwfr.
    econstructor.
    { eapply lookup_program_type; eauto. }
    assumption.
  + on (wfm_frame _ _), invc. on (Forall (wfm_instr _ _) _), invc.
    econstructor; eauto.

- (* SCalcCondNo *)
  econstructor; eauto.
  on >wfm_frame, invcs.
  econstructor; eauto.

- (* SCalcCondYes *)
  econstructor; eauto.
  on >wfm_frame, invcs.
  econstructor; eauto. simpl.
  rewrite forall_app.
  split; eauto.
  on (Forall (wfm_instr _ _) _), invcs.
  on >wfm_instr, invcs.
  assumption.

- (* SCheckPACTZero *)
  econstructor; eauto.
  on >wfm_frame, invcs.
  econstructor; eauto.

- (* SCheckPACTNonZero *)
  econstructor; eauto.
  on >wfm_frame, invcs.
  econstructor; simpl; eauto.

- (* SHavocProcessNo *)
  econstructor; eauto.
  on >wfm_frame, invc.
  econstructor; eauto.

- (* SHavocProcessYes *)
  econstructor; [| econstructor ]; eauto.
  + forward eapply lookup_preserves_wfm as Hwfr; eauto.
    unfold wfm_record in Hwfr.
    econstructor.
    { eapply lookup_program_type; eauto. }
    assumption.
  + on (wfm_frame _ _), invc. on (Forall (wfm_instr _ _) _), invc.
    econstructor; eauto.
Qed.

Theorem star_step_preserves_wfm_state : forall dbp dbt state state' oes,
    dbt = database_program_type dbp ->
    wfm_database dbt dbp ->
    star_step dbp state state' oes ->
    wfm_state dbt state ->
    wfm_state dbt state'.
induction 3.
- auto.
- intro Hwf.
  eapply IHstar_step.
  eapply step_preserves_wfm_state; eauto.
Qed.

Theorem start_handle_preserves_wfm : forall dbp dbt ie fr,
    dbt = database_program_type dbp ->
    wfm_database dbt dbp ->
    wfm_input_event dbt ie ->
    start_handle dbp ie fr ->
    wfm_frame dbt fr.
intros0 Heqdbt Hwfdb Hwfie Hsh.
destruct ie; invcs Hsh.

- (* IProcess *)
  repeat constructor.
  forward eapply lookup_preserves_wfm as Hwfr; eauto.
  unfold wfm_record in Hwfr.
  econstructor; eauto.
  { eapply lookup_program_type; eauto. }

- (* IRunCallback *)
  repeat constructor.
  invcs Hwfie.
  econstructor; eauto.

Qed.


(* Output events are well formed *)

Lemma read_record_field_lookup_ok : forall dbs rn fn val,
    read_record_field dbs rn fn = Some val ->
    exists rs, lookup dbs rn = Some rs.
intros0 Hrrf.
unfold read_record_field, bind_option in Hrrf.
break_match; try discriminate Hrrf.
eauto.
Qed.

Theorem output_step_wfm_output_event : forall dbt rn op dbs oe rt,
    dbt = database_state_type dbs ->
    lookup dbt rn = Some rt ->
    wfm_instr dbt rt op ->
    output_step rn op dbs oe ->
    wfm_output_event dbt oe.
intros0 Heqdbt Hrt Hwfi Hstep.
invcs Hstep.

- (* OHwWrite *)
  econstructor. eauto.

- (* OScheduleCallback *)
  econstructor; eauto.
  invcs Hwfi. assumption.

Qed.

Theorem step_wfm_output_event : forall dbt dbp state state' oes,
    dbt = database_program_type dbp ->
    database_state_type (state_dbs state) = dbt ->
    wfm_database dbt dbp ->
    wfm_state dbt state ->
    step dbp state state' oes ->
    Forall (wfm_output_event dbt) oes.
intros0 Heqdbt Hsty Hwfdb Hwfs Hstep.
invcs Hstep; repeat constructor.

- (* SOutput *)
  invc Hwfs. on >wfm_frame, invc. on (Forall (wfm_instr _ _) _), invc. simpl in *.
  eapply output_step_wfm_output_event; eauto.

- (* SPop (produces OTraceEnd) *)
  rewrite <- Hsty.
  forward eapply lookup_map; eauto.
  econstructor. eassumption.

- (* SProcess (produces OTraceBegin) *)
  invc Hwfs. on >wfm_frame, invc. on (Forall (wfm_instr _ _) _), invc.
  on >wfm_instr, invc. on >wfm_record_link, invc.
  econstructor. eassumption.
Qed.

Theorem star_step_wfm_output_event : forall dbt dbp state state' oes,
    dbt = database_program_type dbp ->
    database_state_type (state_dbs state) = dbt ->
    wfm_database dbt dbp ->
    wfm_state dbt state ->
    star_step dbp state state' oes ->
    Forall (wfm_output_event dbt) oes.
induction 5.
{ constructor. }

eapply forall_app. split.
- eapply step_wfm_output_event; eauto.
- eapply IHstar_step; eauto.
  { erewrite <- step_preserves_state_type; eauto. }
  { eapply step_preserves_wfm_state; eauto. }
Qed.


(* system_state_wf *)

Theorem conv_callback_preserves_wf : forall dbt oe now te,
    conv_callback oe now = Some te ->
    wfm_output_event dbt oe ->
    wfm_input_event dbt (te_evt te).
intros0 Hconv Hwf.
destruct oe; simpl in *; try discriminate Hconv.
fancy_injr <- Hconv. simpl.

invc Hwf.
econstructor; eauto.
Qed.

Theorem system_step_preserves_wf : forall time sys sys' oes,
    system_step time sys sys' oes ->
    system_state_wf sys ->
    system_state_wf sys'.
intros0 Hstep Hwf.
invc Hstep.  on >handle, invc.
invc Hwf.  simpl in *.

forward eapply star_step_preserves_state_type; eauto; simpl in *.

econstructor; simpl; eauto; try congruence.
- eapply Forall_forall. intros.
  forward eapply insert_many_from as HH; eauto. destruct HH.
  + forward eapply conv_callbacks_in; eauto.  break_exists. break_and.
    eapply conv_callback_preserves_wf; eauto.
    forward eapply star_step_wfm_output_event; eauto.
    all:simpl. all:try congruence.
      { constructor; eauto.
        eapply start_handle_preserves_wfm; eauto; try congruence.
        rewrite Forall_forall in swf_evts_wfm.
        rewrite swf_dbt_dbp. eapply swf_evts_wfm. simpl. eauto. }
    rewrite Forall_forall in *.
    do 2 on _, fun H => rewrite <- H. eauto.
  + on (_ dbs = _ dbs'), fun H => rewrite <- H.
    rewrite Forall_forall in *. eapply swf_evts_wfm.
    simpl. eauto.
Qed.

Require Import Arith.
Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import Sorted.
Require Import Psatz.


Require Import v1.NeutronTactics.
Require Import v1.Util.
Require Import v1.Multi.

Require Import epics.Opcodes.
Require Import epics.Step.
Require Import epics.Types.
Require Import util.ListLemmas.



Inductive suffix_step :=
| Drop
| Open
| Callback.

Fixpoint suffix_by steps ops :=
    match steps with
    | [] => ops
    | Drop :: steps =>
            match ops with
            | [] => []
            | op :: ops => suffix_by steps ops
            end
    | Open :: steps =>
            match ops with
            | [] => []
            | MCalcCond _ _ _ body :: ops =>
                    suffix_by steps (body ++ ops)
            | MScheduleCallback _ code :: ops =>
                    suffix_by steps (code ++ ops)
            | _ :: ops =>
                    suffix_by steps ops
            end
    | Callback :: steps =>
            match ops with
            | [] => []
            | MScheduleCallback _ code :: ops =>
                    suffix_by steps code
            | _ :: ops =>
                    suffix_by steps ops
            end
    end.

Definition suffix_of xs ys := exists steps, suffix_by steps xs = ys.

Lemma nil_suffix_by : forall steps,
    suffix_by steps [] = [].
induction steps.
  { reflexivity. }
destruct a; simpl; reflexivity.
Qed.

Lemma suffix_by_trans : forall steps steps' ops,
    suffix_by steps' (suffix_by steps ops) = suffix_by (steps ++ steps') ops.
induction steps; intros.
- simpl. reflexivity.
- replace ((a :: steps) ++ steps') with (a :: steps ++ steps') by eauto.
  destruct a, ops; eauto using nil_suffix_by.
  + destruct m; eauto.
  + destruct m; eauto.
Qed.


Lemma nil_suffix : forall xs, suffix_of xs [].
induction xs.
- exists []. reflexivity.
- unfold suffix_of in *. destruct IHxs as [steps ?]. 
  exists (Drop :: steps). simpl. assumption.
Qed.

Lemma suffix_trans : forall xs xs' xs'',
    suffix_of xs xs' ->
    suffix_of xs' xs'' ->
    suffix_of xs xs''.
intros0 Hsuf1 Hsuf2.
destruct Hsuf1 as [steps1 ?].
destruct Hsuf2 as [steps2 ?].
exists (steps1 ++ steps2).
rewrite <- suffix_by_trans. congruence.
Qed.

Lemma suffix_tail : forall xs x' xs',
    suffix_of xs (x' :: xs') ->
    suffix_of xs xs'.
intros0 Hsuf.  destruct Hsuf as [steps ?].
exists (steps ++ [Drop]).
rewrite <- suffix_by_trans. simpl. find_rewrite. reflexivity.
Qed.

Lemma suffix_tail' : forall xs xs'1 xs'2,
    suffix_of xs (xs'1 ++ xs'2) ->
    suffix_of xs xs'2.
induction xs'1; simpl; intros0 Hsuf.
- assumption.
- eapply IHxs'1. eapply suffix_tail. eassumption.
Qed.

Lemma suffix_refl : forall xs, suffix_of xs xs.
intros. exists []. reflexivity.
Qed.
Hint Resolve suffix_refl.

Lemma suffix_CalcCond : forall xs fn_cur fn_prev oopt body rest,
    suffix_of xs (MCalcCond fn_cur fn_prev oopt body :: rest) ->
    suffix_of xs (body ++ rest).
destruct 1 as [steps ?].  exists (steps ++ [Open]).
rewrite <- suffix_by_trans. find_rewrite. simpl. reflexivity.
Qed.

Lemma suffix_ScheduleCallback_now : forall xs delay code rest,
    suffix_of xs (MScheduleCallback delay code :: rest) ->
    suffix_of xs rest.
destruct 1 as [steps ?].  exists (steps ++ [Drop]).
rewrite <- suffix_by_trans. find_rewrite. simpl. reflexivity.
Qed.

Lemma suffix_ScheduleCallback_later : forall xs delay code rest,
    suffix_of xs (MScheduleCallback delay code :: rest) ->
    suffix_of xs code.
destruct 1 as [steps ?].  exists (steps ++ [Callback]).
rewrite <- suffix_by_trans. find_rewrite. simpl. reflexivity.
Qed.



Inductive record_code_ok (dbp : database_program) : record_name -> list micro -> Prop :=
| RcOk : forall rn code rp,
        lookup dbp rn = Some rp ->
        suffix_of (rp_code rp) code ->
        record_code_ok dbp rn code.

Definition frame_ok dbp frame := record_code_ok dbp (frame_rn frame) (frame_code frame).

Definition state_ok dbp state := Forall (frame_ok dbp) (state_stk state).

Definition output_event_ok dbp oe :=
    match oe with
    | OScheduleCallback _ rn code => record_code_ok dbp rn code
    | _ => True
    end.

Definition input_event_ok dbp ie :=
    match ie with
    | IRunCallback rn code => record_code_ok dbp rn code
    | _ => True
    end.


Lemma output_step_ok : forall dbp rn op ops dbs oe,
    output_step rn op dbs oe ->
    record_code_ok dbp rn (op :: ops) ->
    output_event_ok dbp oe.
inversion 1; inversion 1; econstructor; eauto.
eapply suffix_trans; [ eassumption | ].
eapply suffix_ScheduleCallback_later; eauto.
Qed.


Theorem step_state_ok : forall dbp state state' oes,
    step dbp state state' oes ->
    state_ok dbp state ->
    state_ok dbp state'.
destruct 1; intros0 Hok; unfold state_ok, state_stk in *.

- (* db_step *)
  invc Hok. constructor; auto.
  on >frame_ok, invc. econstructor; eauto.
  eapply suffix_tail. eassumption.

- (* output_step *)
  invc Hok. constructor; auto.
  on >frame_ok, invc. econstructor; eauto.
  eapply suffix_tail. eassumption.

- (* stack pop *) 
  invc Hok. assumption.

- (* Process *)
  invc Hok.  constructor.
  + econstructor; eauto.
  + constructor; eauto.
    on >frame_ok, invc. econstructor; eauto.
    eauto using suffix_tail.

- (* CalcCond (no) *)
  invc Hok.  constructor; eauto.
  on >frame_ok, invc.  econstructor; eauto using suffix_tail.

- (* CalcCond (yes) *)
  invc Hok.  constructor; eauto.
  on >frame_ok, invc.  econstructor; simpl; eauto using suffix_CalcCond.

- (* CheckPACT (zero) *)
  invc Hok.  constructor; eauto.
  on >frame_ok, invc.  econstructor; eauto using suffix_tail.

- (* CheckPACT (nonzero) *)
  invc Hok.  constructor; eauto.
  on >frame_ok, invc.  econstructor; eauto using nil_suffix.

- (* HavocProcess (no) *)
  invc Hok.  constructor; eauto.
  on >frame_ok, invc.  econstructor; eauto using suffix_tail.

- (* HavocProcess (yes) *)
  invc Hok.  constructor.
  + econstructor; eauto.
  + constructor; eauto.
    on >frame_ok, invc. econstructor; eauto.
    eauto using suffix_tail.

Qed.

Theorem step_output_event_ok : forall dbp state state' oes,
    step dbp state state' oes ->
    state_ok dbp state ->
    Forall (output_event_ok dbp) oes.
destruct 1; intros0 Hok; try solve [eauto | repeat constructor].
constructor; eauto. eapply output_step_ok; eauto.
invc Hok. eassumption.
Qed.

Theorem star_step_output_event_ok : forall dbp state state' oes,
    star_step dbp state state' oes ->
    state_ok dbp state ->
    Forall (output_event_ok dbp) oes.
induction 1; intros; eauto.
eapply forall_app. split.
- eapply step_output_event_ok; eauto.
- eapply IHstar_step. eapply step_state_ok; eauto.
Qed.

Theorem star_step_state_ok : forall dbp state state' oes,
    star_step dbp state state' oes ->
    state_ok dbp state ->
    state_ok dbp state'.
induction 1; intros0 Hok; eauto using step_state_ok.
Qed.

(* TODO
Theorem start_handle_frame_ok : forall dbp ie frame,
    start_handle dbp ie frame ->
    input_event_ok dbp ie ->
    frame_ok dbp frame.
inversion 1; inversion 1; eauto.
econstructor; eauto.
Qed.

Theorem handle_output_event_ok : forall dbp dbs ie dbs' oes,
    handle dbp dbs ie dbs' oes ->
    input_event_ok dbp ie ->
    Forall (output_event_ok dbp) oes.
inversion 1; subst; intros0 Hok; eauto.
econstructor; eauto; try exact I.
econstructor; eauto; try exact I.
eapply star_step_output_event_ok; eauto.
unfold state_ok. constructor; eauto.
eapply start_handle_frame_ok; eauto.
Qed.
*)



Lemma suffix_by_forall : forall P ops steps,
    Forall (MicroForall P) ops ->
    Forall (MicroForall P) (suffix_by steps ops).
first_induction steps; intros; eauto.
rename a into step. destruct step, ops; simpl; eauto.

- on (Forall _ (_ :: _)), invc.
  destruct m; eauto.
  + on (MicroForall _ _), invc; try contradiction.
    eapply IHsteps. eapply forall_app; eauto.
  + on (MicroForall _ _), invc; try contradiction.
    eapply IHsteps. eapply forall_app; eauto.

- on (Forall _ (_ :: _)), invc.
  destruct m; eauto.
  + on (MicroForall _ _), invc; try contradiction.
    eapply IHsteps. assumption.
Qed.

Lemma suffix_forall : forall P ops ops',
    suffix_of ops ops' ->
    Forall (MicroForall P) ops ->
    Forall (MicroForall P) ops'.
intros0 Hsuf Hfa.
invc Hsuf. eauto using suffix_by_forall.
Qed.

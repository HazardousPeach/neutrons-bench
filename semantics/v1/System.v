Require Import Arith.
Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import Sorted.
Require Import Omega.

Require Import v1.Step.
Require Import v1.Queue.
Require Import v1.NeutronTactics.
Require Import v1.Terminate.


Definition conv_callback oe now :=
    match oe with
    | OScheduleCallback delay rn ops =>
            Some (TsEvent (now + delay) (IRunCallback rn ops))
    | _ => None
    end.

Fixpoint conv_callbacks oes now :=
    match oes with
    | [] => []
    | oe :: oes' =>
            match conv_callback oe now with
            | None => conv_callbacks oes' now
            | Some ie => ie :: conv_callbacks oes' now
            end
    end.

Lemma conv_callbacks_forall : forall oes now,
    Forall
        (fun ie => exists oe, In oe oes /\ conv_callback oe now = Some ie)
        (conv_callbacks oes now).
first_induction oes; intros; simpl in *.
{ constructor. }

break_match.

- constructor; eauto.
  eapply Forall_impl; eauto.  cbv beta.
  intros. break_exists. break_and.
  eexists. eauto.

- eauto.
  eapply Forall_impl; eauto.  cbv beta.
  intros. break_exists. break_and.
  eexists. eauto.
Qed.

Lemma conv_callbacks_in : forall oes now ies ie,
    conv_callbacks oes now = ies ->
    In ie ies ->
    exists oe, In oe oes /\ conv_callback oe now = Some ie.
intros0 Hconv Hin.
forward eapply conv_callbacks_forall with (oes := oes) (now := now); eauto.
rewrite Forall_forall in *.
subst. eauto.
Qed.


(* The entire state of the system. *)
Record system_state : Set := SystemState
    { sys_dbp : database_program
    (* `dbm` needs to be in the system_state because it's needed to perform
       well-founded recursion. *)
    ; sys_dbm : database_metric
    ; sys_dbs : database_state
    ; sys_evts : list timestamped_event
    }.

Section insert.
    Set Implicit Arguments.

    Variable A : Type.

    Inductive insert_one : A -> list A -> list A -> Prop :=
    | InsHere : forall x xs, insert_one x xs (x :: xs)
    | InsThere : forall x y ys ys',
            insert_one x ys ys' ->
            insert_one x (y :: ys) (y :: ys').

    Lemma insert_one_in : forall x xs xs',
        insert_one x xs xs' ->
        In x xs'.
    induction 1; simpl; eauto.
    Qed.

    Lemma insert_one_from : forall x xs xs' z,
        insert_one x xs xs' ->
        In z xs' ->
        z = x \/ In z xs.
    induction 1; intros0 Hin.
    - destruct Hin; eauto.
    - destruct Hin; eauto.
      + right. unfold In. eauto.
      + spec IHinsert_one by assumption. firstorder.
    Qed.

    Inductive insert_many : list A -> list A -> list A -> Prop :=
    | ImNil : forall ys, insert_many [] ys ys
    | ImCons : forall x xs ys ys' ys'',
            insert_one x ys ys' ->
            insert_many xs ys' ys'' ->
            insert_many (x :: xs) ys ys''.

    Lemma insert_many_from : forall xs ys ys' z,
        insert_many xs ys ys' ->
        In z ys' ->
        In z xs \/ In z ys.
    induction 1; intros0 Hin.
    - eauto.
    - spec IHinsert_many by assumption.
      destruct IHinsert_many; try eauto using in_cons.
      forward eapply insert_one_from as HH; eauto. destruct HH.
      + left. simpl. eauto.
      + right. assumption.
    Qed.

End insert.

(* Process one event from the queue *)
Inductive system_step : time -> system_state -> system_state -> list output_event -> Prop :=
| SystemStep : forall now dbp dbm dbs dbs' evt evts evts' oes,
        (* Run the first event *)
        handle dbp dbs (te_evt evt) dbs' oes ->
        (* Generate new events for any scheduled callbacks *)
        insert_many (conv_callbacks oes now) evts evts' ->
        (* Event list should be sorted before and after *)
        StronglySorted te_le (evt :: evts) ->
        StronglySorted te_le evts' ->
        system_step now
                (SystemState dbp dbm dbs (evt :: evts))
                (SystemState dbp dbm dbs' evts')
                oes.

(*
Inductive system_run_until : time -> system_state -> system_state -> list output_event -> Prop :=
| SruDone : forall until sys,
        Forall (fun evt => te_when evt > until) (sys_evts sys) ->
        system_run_until until state state []
| SruMore : forall until sys sys' sys'' oes1 oes2,

        *)

Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import Omega.

Require Import v1.Util.
Require Import v1.Multi.
Require Import v1.NeutronTactics.

Require Import epics.SpecOpcodes.
Require Import epics.SpecRecords.
Require Import epics.SpecStep.
Require Import epics.SpecTypes.


Definition event_queue := list (Z * input_event).

(* Add event `ie` to the event queue `q` at time `t`.  The new event is
 * inserted after all other events with time equal to `t`, but before any
 * events with time greater than `t`.
 *
 * This is an awfully strict spec (one could imagine requiring only that the
 * event is inserted *somewhere* maintaining sorted order, rather than strictly
 * at the end of its equivalence class) but seems to reflect EPICS Base
 * behavior.*)
Fixpoint enqueue_event t ie (q : event_queue) :=
    match q with
    | [] => [(t, ie)]
    | (t', ie') :: q =>
            if Z_gt_dec t' t then
                (t, ie) :: (t', ie') :: q
            else
                (t', ie') :: enqueue_event t ie q
    end.

(* Handle an output event by possibly enqueueing a new input event.  Only
 * certain kinds of output events queue new inputs - on the rest, this is a
 * no-op.  `t` is the timestamp when `oe` occurred. *)
Definition handle_output_event t oe q :=
    match oe with
    | OScheduleCallback delay rn ops =>
            enqueue_event (t + delay) (IRunCallback rn ops) q
    | _ => q
    end.

Fixpoint handle_output_events t oes q :=
    match oes with
    | [] => q
    | oe :: oes' =>
            let q' := handle_output_event t oe q in
            handle_output_events t oes' q'
    end.


(* Relation for handling a single input event, transforming the current
 * database_state and producing some output_events. *)
Inductive event_loop_step (dbp : database_program) :
    database_state -> input_event -> database_state -> list output_event -> Prop :=
| HeProcess : forall dbs rn dbs' oes rp,
        lookup dbp rn = Some rp ->
        star_step dbp
            (State dbs [Frame rn (rp_code rp)])
            (State dbs' [])
            oes ->
        event_loop_step dbp dbs (IProcess rn) dbs' oes
| HeRunCallback : forall dbs rn ops dbs' oes,
        star_step dbp
            (State dbs [Frame rn ops])
            (State dbs' [])
            oes ->
        event_loop_step dbp dbs (IRunCallback rn ops) dbs' oes
.

(* Relation for running the event loop to quiescence (empty queue). *)
Inductive event_loop_star_step (dbp : database_program) :
    database_state -> event_queue -> database_state -> list output_event -> Prop :=
| EssNil : forall dbs,
        event_loop_star_step dbp dbs [] dbs []
| EssCons : forall dbs t ie q dbs' dbs'' oes1 oes2,
        event_loop_step dbp dbs ie dbs' oes1 ->
        let q' := handle_output_events t oes1 q in
        event_loop_star_step dbp dbs' q' dbs'' oes2 ->
        event_loop_star_step dbp dbs ((t, ie) :: q) dbs'' (oes1 ++ oes2).

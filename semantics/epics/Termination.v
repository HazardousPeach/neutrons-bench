Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Omega.
Require Import Relation_Operators.
Require Import Wellfounded.Lexicographic_Product.

Require Import v1.NeutronTactics.
Require Import v1.Multi.
Require Import v1.Util.

Require Import epics.Types.
Require Import epics.Records.
Require Import epics.Opcodes.
Require Import epics.Step.
Require Import epics.Wf.
Require Import util.ListLemmas.

Set Default Timeout 10.
Set Implicit Arguments.


Definition record_metric := nat.
Definition database_metric := list nat.
Notation lookup_metric := (@lookup nat).

(* Relations giving the time taken to execute various operations. *)

Inductive instr_time (dbm : database_metric) : nat -> micro -> Prop :=
| ItSetConst : forall fn val, instr_time dbm 1 (MSetConst fn val)
| ItCopy : forall fn_src src_ty fn_dest dest_ty,
        instr_time dbm 1 (MCopy fn_src src_ty fn_dest dest_ty)
| ItReadLink : forall il il_ty fn f_ty, instr_time dbm 1 (MReadLink il il_ty fn f_ty)
| ItWriteLink : forall fn f_ty ol ol_ty, instr_time dbm 1 (MWriteLink fn f_ty ol ol_ty)
| ItProcess : forall fl rtime,
        lookup_metric dbm (rl_rn fl) = Some rtime ->
        instr_time dbm (S rtime) (MProcess fl)
| ItCalculate : forall expr fn_out, instr_time dbm 1 (MCalculate expr fn_out)
| ItHwRead : forall fn f_ty, instr_time dbm 1 (MHwRead fn f_ty)
| ItHwWrite : forall fn f_ty out_ty, instr_time dbm 1 (MHwWrite fn f_ty out_ty)
| ItCalcCond : forall fn_cur fn_prev oopt body btime,
        Forall2 (instr_time dbm) btime body ->
        instr_time dbm (S (fold_left Nat.add btime 0)) (MCalcCond fn_cur fn_prev oopt body)
| ItScheduleCallback : forall delay code, instr_time dbm 1 (MScheduleCallback delay code)
| ItCheckPACT : instr_time dbm 1 (MCheckPACT)
| ItUnkRead : forall fn f_ty, instr_time dbm 1 (MUnkRead fn f_ty)
| ItUnkWrite : instr_time dbm 1 MUnkWrite
| ItHavocUpdate : instr_time dbm 1 (MHavocUpdate)
| ItHavocWrite : forall ol ol_ty, instr_time dbm 1 (MHavocWrite ol ol_ty)
| ItHavocProcess : forall fl rtime,
        lookup_metric dbm (rl_rn fl) = Some rtime ->
        instr_time dbm (S rtime) (MHavocProcess fl)
.

Inductive record_time' (dbm : database_metric) : nat -> list micro -> Prop :=
| RtNil : record_time' dbm 0 []
| RtCons : forall op t1 ops t2,
        instr_time dbm t1 op ->
        record_time' dbm t2 ops ->
        record_time' dbm (t1 + t2) (op :: ops).

Inductive record_time (dbm : database_metric) : nat -> record_program -> Prop :=
| RecordTime : forall t rp,
        record_time' dbm t (rp_code rp) ->
        record_time dbm t rp.

Inductive database_time' (dbm : database_metric) : database_metric -> database_program -> Prop :=
| DtNil : database_time' dbm [] []
| DtCons : forall t ts rp dbp,
        record_time dbm t rp ->
        database_time' dbm ts dbp ->
        database_time' dbm (t :: ts) (rp :: dbp).

Inductive database_time (dbm : database_metric) : database_program -> Prop :=
| DatabaseTime : forall dbp,
        database_time' dbm dbm dbp ->
        database_time dbm dbp.

(* If `database_time dbm dbp` holds, then `dbm` accurately reflects the time
   required to process each record in `dbp`.  This also implies that each
   record requires only finite time to process. *)


(* Cycle checker / time measurement *)

(* The cycle checker works in a sort of translation-validation style.  It first
   computes the metric for each record in the database, then checks that those
   metrics are actually valid (producing a proof).  The first step can fail by
   running out of fuel (but that should happen only if there is a cycle). *)

(* A note on "quality of implementation issues":

   The count_* and check_* functions can be written "badly", such that they
   return None more often than they should.  There is no verification in place
   to prevent this from happening.  Thus, these functions must be written
   carefully to ensure correctness.

   The measure_* functions below *are* verified, so we can be more flexible
   with their definitions.
 *)

(* Count the required time. *)

Inductive error :=
| TeNoSuchRecord (rn : record_name)
| TeOutOfFuel
| TeValidationFailed
| TeInRecord (rn : record_name) (e : error)
.

Definition context {A} (ctx : error -> error) (r : A + list error) : A + list error :=
    match r with
    | inl x => inl x
    | inr e => inr (map ctx e)
    end.

Definition bind_result {A B} (f : A + list error) (g : A -> B + list error) : B + list error :=
    match f with
    | inl x => g x
    | inr errs => inr errs
    end.

Local Notation "x '>>=' f" := (bind_result x f)
    (at level 42, left associativity).

Local Notation "'do' x '<-' m ';;' k" := (bind_result m (fun x => k))
    (at level 200, x ident, right associativity).


Fixpoint count_instr (loop : record_name -> nat + list error) (op : micro) : nat + list error :=
    let fix count_instr_list ops : nat + list error :=
        match ops with
        | [] => inl 0
        | op :: ops =>
                count_instr loop op >>= fun t1 =>
                count_instr_list ops >>= fun t2 =>
                inl (t1 + t2)
        end in
    match op with
    | MSetConst _ _ => inl 1
    | MCopy _ _ _ _ => inl 1
    | MReadLink _ _ _ _ => inl 1
    | MWriteLink _ _ _ _ => inl 1
    | MProcess fl =>
            loop (rl_rn fl) >>= fun t => inl (S t)
    | MCalculate _ _ => inl 1
    | MHwRead _ _ => inl 1
    | MHwWrite _ _ _ => inl 1
    | MCalcCond _ _ _ body =>
            count_instr_list body >>= fun t => inl (S t)
    | MScheduleCallback _ _ => inl 1
    | MCheckPACT => inl 1
    | MUnkRead _ _ => inl 1
    | MUnkWrite => inl 1
    | MHavocUpdate => inl 1
    | MHavocWrite _ _ => inl 1
    | MHavocProcess fl =>
            loop (rl_rn fl) >>= fun t => inl (S t)
    end.

Fixpoint count_record' (loop : record_name -> nat + list error) (ops : list micro) :
        nat + list error :=
    match ops with
    | [] => inl 0
    | op :: ops =>
            count_instr loop op >>= fun m1 =>
            count_record' loop ops >>= fun m2 =>
            inl (m1 + m2)
    end.

Fixpoint count_record fuel dbp (rp : record_program) {struct fuel} : nat + list error :=
    match fuel with
    | 0 => inr [TeOutOfFuel]
    | S fuel' =>
            let loop := fun rn =>
                match lookup_program dbp rn with
                | Some x => inl x
                | None => inr [TeNoSuchRecord rn]
                end >>= fun rp =>
                context (TeInRecord rn) (count_record fuel' dbp rp) in
            count_record' loop (rp_code rp)
    end.

Fixpoint count_database' fuel dbp rps0 rn : database_metric + list error :=
    match rps0 with
    | [] => inl []
    | rp :: rps =>
            let r1 := count_record fuel dbp rp in
            let r2 := count_database' fuel dbp rps (S rn) in

            match r1, r2 with
            | inl m, inl ms => inl (m :: ms)
            | inr e1, inr e2 => inr (e1 ++ e2)
            | inr e1, inl _ => inr e1
            | inl _, inr e2 => inr e2
            end
    end.

Definition count_database_with_fuel dbp fuel : database_metric + list error :=
    count_database' fuel dbp dbp 0.

Definition count_database dbp : database_metric + list error :=
    (* Give a little extra fuel so we don't need to worry about zero vs. one
     * cutoff in the deepest recursion *)
    count_database_with_fuel dbp (5 + length dbp).

(* Find records that have unbounded execution time (ignoring PACT cycle-breaking) *)
(*
Definition find_loops dbp : option (list (record_name * nat * nat)) :=
    let fuel := 5 + length dbp in
    map_partial (count_record fuel dbp) dbp >>= fun ts1 =>
    map_partial (count_record (S fuel) dbp) dbp >>= fun ts2 =>
    map_partial (fun rn_t1 =>
        let '(rn, t1) := rn_t1 in
        nth_error ts2 rn >>= fun t2 =>
        Some (rn, t1, t2)) (numbered ts1) >>= fun ts12 =>
    Some (filter (fun rn_t1_t2 =>
        let '(rn, t1, t2) := rn_t1_t2 in
        if eq_nat_dec t1 t2 then false else true) ts12).
*)

(* Check that the counts are valid. *)

Definition check_instr_time dbm : forall op, option { m | instr_time dbm m op }.
induction op using micro_rect_mut
    with (Pl := fun ops => option { ms | Forall2 (instr_time dbm) ms ops });
(* Solve non-recursive cases with m = 1 *)
try solve [ apply Some; exists 1; econstructor ].

(* MProcess *)
- destruct (lookup dbm (rl_rn fl)) as [ rm | ] eqn:?; [ | apply None ].
  apply Some. exists (S rm). econstructor. assumption.

(* MCalcCond *)
- destruct (IHop) as [ [ms Hms] | ]; [ | exact None ].
  eapply Some. exists (S (fold_left Nat.add ms 0)). constructor; assumption.

(* MHavocProcess *)
- destruct (lookup dbm (rl_rn fl)) as [ rm | ] eqn:?; [ | apply None ].
  apply Some. exists (S rm). econstructor. assumption.

(* nil *)
- eapply Some. exists []. constructor.

(* cons *)
- destruct (IHop) as [ [m Hm] | ]; [ | exact None ].
  destruct (IHop0) as [ [ms Hms] | ]; [ | exact None ].
  eapply Some. exists (m :: ms). constructor; assumption.
Defined.

Fixpoint check_record_time' dbm ops : option { m | record_time' dbm m ops }.
rename check_record_time' into loop.
destruct ops as [ | op ops ].
{ (* nil *) apply Some. exists 0. constructor. }

destruct (check_instr_time dbm op) as [ [m1 Hm1] | ]; [ | apply None ].
destruct (loop dbm ops) as [ [m2 Hm2] | ]; [ | apply None ].
apply Some. exists (m1 + m2).
constructor; assumption.
Defined.

Definition check_record_time dbm rp : option { m | record_time dbm m rp }.
destruct (check_record_time' dbm (rp_code rp)) as [ [m Hm] | ]; [ | apply None ].
apply Some. exists m.
constructor. assumption.
Defined.

Fixpoint check_database_time' dbm ts dbp : option (database_time' dbm ts dbp).
rename check_database_time' into loop.
destruct ts as [ | t ts ];
destruct dbp as [ | rp dbp ].
{ (* nil *) apply Some. constructor. }
{ (* nil, cons *) apply None. }
{ (* cons, nil *) apply None. }

destruct (check_record_time dbm rp) as [ [t' ?H] | ]; [ | apply None ].
destruct (eq_nat_dec t t'); [ subst t' | apply None ].
destruct (loop dbm ts dbp) as [ ?H | ]; [ | apply None ].
apply Some. econstructor; eassumption.
Defined.

(* Main entry point for cycle checker *)
Definition check_database_time_with_fuel dbp (fuel : nat) :
    { dbm | database_time dbm dbp } + list error.
destruct (count_database_with_fuel dbp fuel) as [ dbm | errs ]; [ | exact (inr errs) ].
destruct (check_database_time' dbm dbm dbp) as [ Hdbm | ];
        [ | exact (inr [TeValidationFailed]) ].
apply inl. exists dbm. constructor. assumption.
Defined.

Definition check_database_time dbp : { dbm | database_time dbm dbp } + list error.
destruct (count_database dbp) as [ dbm | errs ]; [ | exact (inr errs) ].
destruct (check_database_time' dbm dbm dbp) as [ Hdbm | ];
        [ | exact (inr [TeValidationFailed]) ].
apply inl. exists dbm. constructor. assumption.
Defined.


(* Decreasing relation *)

(* Return the total time required to handle each instruction.  May be >1 if the
   instruction triggers processing of an additional record. *)
Fixpoint measure_instr dbm m : nat :=
    let fix measure_instr_list ms : nat :=
        match ms with
        | [] => 0
        | m :: ms =>
                measure_instr dbm m +
                measure_instr_list ms
        end in
    match m with
    | MSetConst _ _ => 1
    | MCopy _ _ _ _ => 1
    | MReadLink _ _ _ _ => 1
    | MWriteLink _ _ _ _ => 1
    | MProcess fl =>
            match lookup dbm (rl_rn fl) with
            | Some t => S t
            | None => 0
            end
    | MCalculate _ _ => 1
    | MHwRead _ _ => 1
    | MHwWrite _ _ _ => 1
    | MCalcCond _ _ _ body => S (measure_instr_list body)
    | MScheduleCallback _ _ => 1
    | MCheckPACT => 1
    | MUnkRead _ _ => 1
    | MUnkWrite => 1
    | MHavocUpdate => 1
    | MHavocWrite _ _ => 1
    | MHavocProcess fl =>
            match lookup dbm (rl_rn fl) with
            | Some t => S t
            | None => 0
            end
    end.

Definition measure_instrs dbm ops :=
    let ts := map (measure_instr dbm) ops in
    fold_left Nat.add ts 0.

Definition measure_frame dbm frame :=
    measure_instrs dbm (frame_code frame).

Definition measure_state dbm state :=
    let ts := map (measure_frame dbm) (state_stk state) in
    fold_left Nat.add ts 0.

Definition state_lt dbm state state' :=
    (* Two possibilities: *)
    (*  1) Run an instruction.  This may have any effect on the stack size.
           (In particular, MProcess pushes a new frame, though the frame's
           total cost is one less than the cost of the MProcess.) *)
    measure_state dbm state < measure_state dbm state' \/
    (*  2) Pop an empty stack frame.  We could also use <= for measure here,
           since we only need to prohibit increasing the instruction count.
           (Otherwise, the program could alternately run an instruction and
           push a frame, then pop the frame and add new instructions, forever.)
     *)
    (measure_state dbm state = measure_state dbm state' /\
     length (state_stk state) < length (state_stk state')).


(* misc. lemmas *)
Lemma database_time'_length : forall dbm ts dbp,
    database_time' dbm ts dbp ->
    length ts = length dbp.
first_induction ts; intros0 Htime;
destruct dbp; invcs Htime.
- reflexivity.
- forward eapply IHts; eauto.
Qed.

Lemma database_time_length : forall dbm dbp,
    database_time dbm dbp ->
    length dbm = length dbp.
intros0 Htime. inversion Htime. eapply database_time'_length; eauto.
Qed.

Lemma measure_instr_ok : forall dbm dbp,
    database_time dbm dbp ->
    forall m rt,
    wfm_instr (database_program_type dbp) rt m ->
    instr_time dbm (measure_instr dbm m) m.
intros0 Htime.
induction m using micro_ind';
intros0 Hwf;
simpl; try solve [ constructor ].

(* MProcess *)
- break_match; cycle 1.
  { (* None *)
    exfalso. rewrite nth_error_None in *.
    invcs Hwf. on >wfm_record_link, invcs.
    forward eapply lookup_Some_lt; eauto.
    unfold database_program_type in *. rewrite map_length in *.
    forward eapply database_time_length; eauto.
    omega. }
  constructor. assumption.

(* MCalcCond *)
- set (btime := map (measure_instr dbm) body).
  (* Luckily, this vague pattern actually grabs the right ((fix ...) body) expr *)
  replace (_ body) with (fold_left Nat.add btime 0); cycle 1.
  { clear H Hwf. subst btime. induction body; simpl.
    - reflexivity.
    - rewrite sum_init. f_equal. eapply IHbody. }
  invc Hwf. constructor. induction body; constructor.
  + rewrite Forall_forall in H. eapply H; simpl; eauto.
    on (Forall _ (_ :: _)), fun H => (rewrite Forall_forall in H; eapply H).
    simpl. eauto.
  + repeat on (Forall _ (_ :: _)), invc. eapply IHbody; eauto. 

(* MHavocProcess *)
- break_match; cycle 1.
  { (* None *)
    exfalso. rewrite nth_error_None in *.
    invcs Hwf. on >wfm_record_link, invcs.
    forward eapply lookup_Some_lt; eauto.
    unfold database_program_type in *. rewrite map_length in *.
    forward eapply database_time_length; eauto.
    omega. }
  constructor. assumption.
Defined.

Lemma instr_time_pos : forall dbm t op,
    instr_time dbm t op ->
    0 < t.
intros0 Htime. invcs Htime; omega.
Qed.

Lemma measure_instrs_nil : forall dbm,
    measure_instrs dbm [] = 0.
reflexivity.
Qed.

Lemma measure_instrs_cons : forall dbm op ops,
    measure_instrs dbm (op :: ops) = measure_instr dbm op + measure_instrs dbm ops.
intros.
unfold measure_instrs.
rewrite map_cons. rewrite sum_cons. reflexivity.
Qed.

Lemma measure_instrs_app : forall dbm ops1 ops2,
    measure_instrs dbm (ops1 ++ ops2) = measure_instrs dbm ops1 + measure_instrs dbm ops2.
intros.
unfold measure_instrs.
rewrite map_app. rewrite sum_app. reflexivity.
Qed.

Lemma lookup_metric_record_time' : forall dbp ts dbm rn rp t,
    database_time' dbm ts dbp ->
    lookup dbp rn = Some rp ->
    lookup ts rn = Some t ->
    record_time dbm t rp.
first_induction rn; intros0 Htime Hlp Hlt;
destruct dbp; simpl in *; try congruence;
destruct ts; simpl in *; try congruence;
invcs Htime.
- congruence.
- eapply IHrn; eauto.
Qed.

Lemma lookup_metric_record_time : forall dbp dbm rn rp t,
    database_time dbm dbp ->
    lookup dbp rn = Some rp ->
    lookup dbm rn = Some t ->
    record_time dbm t rp.
intros0 Htime Hlp Hlt.
inversion Htime. eapply lookup_metric_record_time'; eauto.
Qed.

Lemma measure_instr_time : forall dbm op t,
    instr_time dbm t op ->
    measure_instr dbm op = t.
induction op using micro_ind';
intros0 Htime; invcs Htime; try reflexivity.
- on (_ = _), fun H => rewrite H. reflexivity.
- f_equal.
  generalize dependent btime; induction body;
  intros0 Hfa2; simpl; invc Hfa2.
  + reflexivity.
  + on (Forall _ (_ :: _)), invc.
    simpl. rewrite sum_init.
    f_equal. { eauto. }
    eapply IHbody; eauto.
- on (_ = _), fun H => rewrite H. reflexivity.
Qed.

Lemma measure_record_time' : forall dbm ops t,
    record_time' dbm t ops ->
    measure_instrs dbm ops = t.
first_induction ops; intros0 Htime; invcs Htime; unfold measure_instrs; simpl in *.
{ reflexivity. }
rewrite sum_init. fold (measure_instrs dbm ops).
erewrite IHops; eauto.
erewrite measure_instr_time; eauto.
Qed.

Lemma lookup_time_measure : forall dbp dbm rn rp t,
    database_time dbm dbp ->
    lookup dbp rn = Some rp ->
    lookup dbm rn = Some t ->
    measure_instrs dbm (rp_code rp) = t.
intros0 Htime Hlp Hlt.
forward eapply lookup_metric_record_time; eauto.
on >record_time, invcs. eapply measure_record_time'. assumption.
Qed.

Lemma measure_instr_pos : forall dbm m  dbp rt,
    database_time dbm dbp ->
    wfm_instr (database_program_type dbp) rt m ->
    0 < measure_instr dbm m.
intros0 Htime Hwf.
eapply instr_time_pos, measure_instr_ok; eassumption.
Qed.


(* Step decreases the metric *)

Theorem step_decreasing : forall dbp dbm dbt state state' oes,
    dbt = database_program_type dbp ->
    wfm_state dbt state ->
    database_time dbm dbp ->
    step dbp state state' oes ->
    state_lt dbm state' state.
intros0 Heqdbt Hwf Htime Hstep.
invcs Hstep.

- (* SDb *)
  left.
  unfold measure_state. simpl. apply sum_lt_init.
  unfold measure_frame, measure_instrs. simpl. apply sum_lt_init.

  invcs Hwf. on (wfm_frame _ _), invcs. on (Forall (wfm_instr _ _) _), invcs.

  eapply instr_time_pos. eapply measure_instr_ok; eauto.

- (* SOutput *)
  left.
  unfold measure_state. simpl. apply sum_lt_init.
  unfold measure_frame, measure_instrs. simpl. apply sum_lt_init.

  invcs Hwf. on (wfm_frame _ _), invcs. on (Forall (wfm_instr _ _) _), invcs.

  eapply instr_time_pos. eapply measure_instr_ok; eauto.

- (* SPop *)
  right. split; [ | simpl; omega ].
  reflexivity. (* does a lot of computation, but gets the right result *)

- (* SProcess *)
  left.
  unfold measure_state. simpl. apply sum_lt_init.
  unfold measure_frame. simpl.
  rewrite measure_instrs_cons.
  apply plus_lt_compat_r.
  forward eapply lookup_length_ex with (ys := dbm) as [t Ht];
      [ on ~lookup_program, fun H => exact H
      | symmetry; eapply database_time_length; eauto | ].
  erewrite lookup_time_measure; eauto.
  erewrite measure_instr_time; cycle 1.
  { econstructor. eassumption. }
  omega.

- (* SCalcCondNo *)
  left.
  unfold measure_state. simpl. apply sum_lt_init.
  unfold measure_frame. simpl.
  rewrite measure_instrs_cons.
  invc Hwf. on >wfm_frame, invc. on (Forall (wfm_instr _ _) _), invc.
  eapply Nat.lt_add_pos_l. eapply measure_instr_pos; eauto.

- (* SCalcCondYes *)
  left.
  unfold measure_state. simpl. apply sum_lt_init.
  unfold measure_frame. simpl.
  rewrite measure_instrs_app. rewrite measure_instrs_cons.
  rewrite <- Nat.add_lt_mono_r.
  simpl. eapply Nat.eq_le_incl. f_equal.
  clear. induction body. { reflexivity. }
  unfold measure_instrs. rewrite map_cons, sum_cons. f_equal. assumption.

- (* SCheckPACTZero *)
  left.
  unfold measure_state. simpl. apply sum_lt_init.
  unfold measure_frame. simpl.
  rewrite measure_instrs_cons.
  simpl. omega.

- (* SCheckPACTNonZero *)
  left.
  unfold measure_state. simpl. apply sum_lt_init.
  unfold measure_frame. simpl.
  rewrite measure_instrs_nil, measure_instrs_cons.
  simpl. omega.

- (* SHavocProcessNo *)
  left.
  unfold measure_state. simpl. apply sum_lt_init.
  unfold measure_frame. simpl.
  rewrite measure_instrs_cons.
  invc Hwf. on >wfm_frame, invc. on (Forall (wfm_instr _ _) _), invc.
  eapply Nat.lt_add_pos_l. eapply measure_instr_pos; eauto.

- (* SHavocProcessYes *)
  left.
  unfold measure_state. simpl. apply sum_lt_init.
  unfold measure_frame. simpl.
  rewrite measure_instrs_cons.
  apply plus_lt_compat_r.
  forward eapply lookup_length_ex with (xs := dbp) (ys := dbm) as [t Ht];
      [ eauto | symmetry; eapply database_time_length; eauto | ].
  erewrite lookup_time_measure; eauto.
  erewrite measure_instr_time; cycle 1.
  { econstructor. eassumption. }
  omega.

Qed.


(* Well-foundedness of state_lt *)

Definition lex_measure := { _ : nat & nat }.
Definition lex_lt :=
    lexprod nat (fun _ => nat) lt (fun _ => lt).

Definition state_lex dbm state : lex_measure :=
    existT _ (measure_state dbm state) (length (state_stk state)).

Lemma state_lt_lex : forall dbm state state',
    state_lt dbm state state' ->
    lex_lt (state_lex dbm state) (state_lex dbm state').
intros0 Hlt. unfold state_lt in Hlt. destruct Hlt as [Hlt | [Heq Hlt]].
- left. assumption.
- unfold state_lex. rewrite Heq. right. assumption.
Qed.

Lemma Acc_func' : forall A (RA : A -> A -> Prop) B (RB : B -> B -> Prop) (f : A -> B) (b : B),
    (forall a1 a2, RA a1 a2 -> RB (f a1) (f a2)) ->
    Acc RB b ->
    forall (a : A), f a = b ->
    Acc RA a.
intros0 Hrel. induction 1. intros0 Heq. constructor.
intros a' ?. eapply H0. rewrite <- Heq. eapply Hrel. eassumption.
reflexivity.
Qed.

Lemma Acc_func : forall A (RA : A -> A -> Prop) B (RB : B -> B -> Prop) (f : A -> B) (a : A),
    (forall a1 a2, RA a1 a2 -> RB (f a1) (f a2)) ->
    Acc RB (f a) ->
    Acc RA a.
intros. eapply Acc_func'; eauto.
Qed.

Lemma lex_lt_well_founded : well_founded lex_lt.
eapply wf_lexprod; eauto using lt_wf.
Qed.

Lemma state_lt_well_founded : forall dbm,
    well_founded (state_lt dbm).
unfold well_founded. intros ? state.
eapply Acc_func with (f := state_lex dbm).
{ eapply state_lt_lex. }
eapply lex_lt_well_founded.
Qed.


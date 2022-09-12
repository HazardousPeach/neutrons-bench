Require Import String.
Require Import List.
Import ListNotations.
Require Import Omega.
Require Import Psatz.
Require Import Sumbool.

Require Import ProofIrrelevance.

Require Import Flocq.Appli.Fappli_IEEE.

Require Import v1.NeutronTactics.

Require Import epics.EventLoop.
Require Import epics.Opcodes.
Require Import epics.Records.
Require Import epics.Step.
Require Import epics.Termination.
Require Import epics.Types.
Require expr.Dbl.
Require Import expr.Expr.
Require Import util.EqDec.

Set Default Timeout 10.
Open Scope string_scope.
Open Scope list_scope.


Inductive trace_event :=
| RecordBegin (rn : record_name) (rs : record_state)
| RecordEnd (rn : record_name) (rs : record_state)
| DbGetLinkValue (v : value)
| DbPutLinkValue (v : value)
| DbHwRead (v : value)
| StrCalcResult (rs : record_state)
.

Definition trace := list trace_event.


Inductive error :=
| TypeMismatch (ty1 ty2 : field_type)
| ValueMismatch (val1 val2 : value)
| RecordStateMismatch (rn : record_name) (rs1 rs2 : record_state)
| ReadRecordFieldFailed (rn : record_name) (fn : field_name)
| WriteRecordFieldFailed (rn : record_name) (fn : field_name) (ty : field_type)
| InvalidExpr (e : expr e_double 12)
| SeekHitBoundary
| EndOfTrace
| EmptyStack
| OutOfFuel
| UnusedEvents (len : nat)

| InRecord (rt : record_type) (rn : record_name) (e : error)
| InOpcode (op : micro) (e : error)
| WithRemainingTrace (len : nat) (e : error)
| WithCallStack (rns : list record_name) (e : error)
| InPop (rn : record_name) (e : error)
| InConversion (val : value) (ty : field_type) (e : error)

| OtherError (msg : string)
| Impossible (msg : string)
.


Module TraceM.

Definition result A : Type := (A * trace) + error.

Definition M A := trace -> result A.

Definition ret {A} (x : A) : M A :=
    fun t => inl (x, t).

Definition bind {A B} (f : M A) (g : A -> M B) : M B :=
    fun t =>
        match f t with
        | inr e => inr e
        | inl (x, t') => g x t'
        end.


Definition fail {A} (err : error) : M A :=
    fun t => inr err.

Definition take : M trace_event :=
    fun t =>
        match t with
        | [] => inr EndOfTrace
        | evt :: t' => inl (evt, t')
        end.

Definition context {A} (ctx : error -> error) (f : M A) : M A :=
    fun t =>
        match f t with
        | inl x => inl x
        | inr e => inr (ctx e)
        end.


Lemma ret_correct : forall {A} (x : A) t x' t',
    ret x t = inl (x', t') ->
    x = x' /\ t = t'.
intros. unfold ret in *. split; congruence.
Qed.

Lemma break_bind : forall {A B} f g t x'' t'',
    @bind A B f g t = inl (x'', t'') ->
    exists x' t',
        f t = inl (x', t') /\
        g x' t' = inl (x'', t'').
intros0 Hbind.
unfold bind in Hbind. break_match; try discriminate.
on (_ * _)%type, fun H => destruct H.
eauto.
Qed.

Lemma bind_ret : forall {A B} x g,
    @bind A B (ret x) g = g x.
intros. reflexivity.
Qed.

Lemma context_inl : forall {A} ctx f x t t',
    @TraceM.context A ctx f t = inl (x, t') ->
    f t = inl (x, t').
intros0 Hctx. unfold TraceM.context in Hctx.
break_match; try discriminate. assumption.
Qed.

End TraceM.

Local Notation "f '>>=' g" := (TraceM.bind f g)
    (at level 42, left associativity).

Local Notation "'do' x '<-' f ';;' g" := (TraceM.bind f (fun x => g))
    (at level 200, x ident, right associativity).

Local Notation fail := TraceM.fail.
Local Notation ret := TraceM.ret.


(* Helpers *)

(* Special equivalence check for doubles: if both values are NaN, then
   the values/fields match, even if the values are not equal by standard `eq`.
   (This can happen because there are many distinct bit patterns that all
   represent NaN. *)
Definition both_nan (v1 v2 : value) :=
    match v1, v2 with
    | VDouble x1, VDouble x2 => is_nan _ _ x1 = true /\ is_nan _ _ x2 = true
    | _, _ => False
    end.

Definition both_nan_dec v1 v2 :
        { both_nan v1 v2 } + { ~ both_nan v1 v2 }.
destruct v1, v2; try solve [right; inversion 1].
rename e into x1, e0 into x2.
simpl.
destruct (is_nan _ _ x1), (is_nan _ _ x2).
{ left; split; reflexivity. }
all: right; inversion 1; congruence.
Defined.


(* Require `x` to be `Some`, otherwise fail with `err`. *)
Definition expect {A} (x : option A) (err : error) : TraceM.M A :=
    match x with
    | None => fail err
    | Some x => ret x
    end.

(* Require `sb` to be `left`, otherwise fail with `err`. *)
Definition assert_sumbool {P Q} (sb : { P } + { Q }) (err : error) : TraceM.M P :=
    match sb with
    | left pf => ret pf
    | right _ => fail err
    end.

(* Require `x` and `y` to be equal, otherwise fail with `err`. *)
Definition assert_eq {A : DecidableEquality} (x y : A) (err : error) : TraceM.M (x = y) :=
    assert_sumbool (eq_dec x y) err.

(* Require `x` and `y` to be equal or to both be NaN, otherwise fail with `err`. *)
Definition assert_eq_nan (x y : value) (err : error) : TraceM.M (x = y \/ both_nan x y) :=
    assert_sumbool (sumbool_or _ _ _ _ (eq_dec x y) (both_nan_dec x y)) err.



(* record state matching *)

(* The main relation is `record_state_match`, defined below.  It essentially
   states that all fields match except those designated by `mismatch_ok`.  The
   relations defined in between are mainly for verification purposes. *)
Definition mismatch_ok (rt : record_type) (fn : field_name) :=
    match rt, fn with
    | _, f_tmp0 => True
    | _, _ => False
    end.

Definition mismatch_ok_dec rt fn :
        { mismatch_ok rt fn } + { ~ mismatch_ok rt fn }.
destruct rt, fn; simpl; eauto.
Defined.

Definition field_matches rt fn (rs1 rs2 : record_state) :=
    forall v1 v2,
        read_field rs1 fn = Some v1 ->
        read_field rs2 fn = Some v2 ->
        v1 = v2 \/ both_nan v1 v2 \/ mismatch_ok rt fn.

Definition field_matches_dec rt fn rs1 rs2 :
    { field_matches rt fn rs1 rs2 } + { ~ field_matches rt fn rs1 rs2 }.
unfold field_matches.

destruct (read_field rs1 fn) as [ v1 | ]; cycle 1.
  { left. intros. discriminate. }
destruct (read_field rs2 fn) as [ v2 | ]; cycle 1.
  { left. intros. discriminate. }

destruct (eq_dec v1 v2).
  { left. intros. left. congruence. }

destruct (both_nan_dec v1 v2).
  { left. intros. right; left. congruence. }

destruct (mismatch_ok_dec rt fn).
  { left. intros. right; right. assumption. }

  { right. intro HH. specialize (HH v1 v2 *** *** ).
    destruct HH as [ | [ | ]]; auto. }
Defined.

Definition fields_match rt (rs1 rs2 : record_state) :=
    (forall fn v1 v2,
        read_field rs1 fn = Some v1 ->
        read_field rs2 fn = Some v2 ->
        v1 = v2 \/ both_nan v1 v2 \/ mismatch_ok rt fn).

Lemma fields_match_forall : forall rt rs1 rs2,
    fields_match rt rs1 rs2 <->
    Forall (fun fn => field_matches rt fn rs1 rs2) all_field_names.
intros. unfold fields_match, field_matches.
rewrite Forall_forall.
pose proof all_field_names_complete.
split; eauto.
Qed.

Definition fields_match_dec rt rs1 rs2 :
    { fields_match rt rs1 rs2 } + { ~ fields_match rt rs1 rs2 }.
assert (HH : { Forall (fun fn => field_matches rt fn rs1 rs2) all_field_names } +
             { ~ Forall (fun fn => field_matches rt fn rs1 rs2) all_field_names }).
  { apply Forall_dec. intro. apply field_matches_dec. }
destruct HH.
- left. rewrite fields_match_forall. assumption.
- right. rewrite <- fields_match_forall in *. assumption.
Defined.

Definition record_state_match (rs1 rs2 : record_state) :=
    record_state_type rs1 = record_state_type rs2 /\
    fields_match (record_state_type rs1) rs1 rs2.

Definition record_state_match_dec rs1 rs2 :
        { record_state_match rs1 rs2 } + { ~ record_state_match rs1 rs2 }.
destruct (eq_dec (record_state_type rs1) (record_state_type rs2)); cycle 1.
  { right. inversion 1. congruence. }
destruct (fields_match_dec (record_state_type rs1) rs1 rs2); cycle 1.
  { right. inversion 1. auto. }

  { left. split; auto. }
Defined.

Definition assert_match rn rs1 rs2 : TraceM.M (record_state_match rs1 rs2) :=
    assert_sumbool (record_state_match_dec rs1 rs2)
        (RecordStateMismatch rn rs1 rs2).



(* Check if `seek` should refuse to seek *past* this event.  Note that it can
   still seek (to* this event, if the event matches `seek`'s predicate. *)
Definition is_seek_boundary (evt : trace_event) :=
    match evt with
    | RecordBegin _ _ => true
    | RecordEnd _ _ => true
    | _ => false
    end.

(* Find an event matching the predicate, and skip to it.  Fails if it would
   need to seek past a begin/end record processing event. *)
Definition seek {A} (f : trace_event -> option A) : TraceM.M A :=
    let fix go t :=
        match t with
        | [] => inr EndOfTrace
        | evt :: t' =>
                match f evt with
                | Some x => inl (x, t)  (* keep the event for now *)
                | None =>
                        if is_seek_boundary evt then
                            inr (WithRemainingTrace (length t) SeekHitBoundary)
                        else
                            go t'
                end
        end in
    go.

Definition seek_take {A} f :=
    do x <- @seek A f;;
    do _ <- TraceM.take;;
    ret x.



(* Interpreter *)

Inductive hint : Set :=
| HNone
| HReadLink
| HWriteLink
.

Require Import ZArith.

Definition check_type ty1 ty2 :=
    assert_eq ty1 ty2 (TypeMismatch ty1 ty2).

Definition check_value val1 val2 :=
    assert_eq_nan val1 val2 (ValueMismatch val1 val2).

Definition run_convert_value_exact (v : value) (ty : field_type) : option value.
simple refine (
    match v, ty with
    | VDouble _, TDouble => Some v
    | VDouble d, TEnum =>
            match FloatAux.B2Z_safe d with
            | Some z =>
                    if Z_le_dec 0 z then
                        if Z_lt_dec z ENUM_MAX then
                            Some (VEnum (EEnum z ltac:(hide; eauto)))
                        else None
                    else None
            | None => None
            end
    | VDouble d, TLong =>
            match FloatAux.B2Z_safe d with
            | Some z =>
                    if Z_le_dec (-LONG_MAX) z then
                        if Z_lt_dec z LONG_MAX then
                            Some (VLong (ELong z ltac:(hide; eauto)))
                        else None
                    else None
            | None => None
            end
    | VDouble _, _ => None

    | VEnum (EEnum z Hlt), TDouble => Some (VDouble (FloatAux.Z2B64 z))
    | VEnum _, TEnum => Some v
    | VEnum (EEnum z Hlt), TLong => Some (VLong (ELong z _))
    | VEnum _, _ => None

    | VLong (ELong z Hlt), TDouble => Some (VDouble (FloatAux.Z2B64 z))
    | VLong (ELong z Hlt), TEnum =>
            if Z_le_dec 0 z then
                if Z_lt_dec z ENUM_MAX then
                    Some (VEnum (EEnum z ltac:(hide; break_and; eauto)))
                else None
            else None
    | VLong (ELong z Hlt), TLong => Some v
    | VLong _, _ => None

    | VString s, TString => Some v
    | VString _, _ => None

    | @VArray ty n a, TArray ty' n' =>
            if eq_dec ty ty' then
                if eq_dec n n' then
                    Some v
                else None
            else None
    | VArray _, _ => None
    end
).

Grab Existential Variables. (* ??? *)
- assert (ENUM_MAX < LONG_MAX)%Z. { unfold ENUM_MAX, LONG_MAX. lia. }
  lia.

Defined.

Definition run_convert_value (v : value) (ty : field_type) (h : hint) : TraceM.M value :=
    match run_convert_value_exact v ty with
    | Some v' => ret v'
    | None =>
            TraceM.context (InConversion v ty) (
                do v' <- seek (fun evt =>
                    match h, evt with
                    | HReadLink, DbGetLinkValue v => Some v
                    | HWriteLink, DbPutLinkValue v => Some v
                    | _, _ => None
                    end);;
                do Hval_ty <- check_type (value_type v') ty;;
                ret v')
    end.

Definition run_read_record_field dbs rn fn :=
    expect (read_record_field dbs rn fn)
        (ReadRecordFieldFailed rn fn).

Definition run_write_record_field dbs rn fn val :=
    expect (write_record_field dbs rn fn val)
        (WriteRecordFieldFailed rn fn (value_type val)).

Definition run_unwrap_double (v : value) :=
    expect (unwrap_double v) (TypeMismatch (value_type v) TDouble).

Definition run_unwrap_enum (v : value) :=
    expect (unwrap_enum v) (TypeMismatch (value_type v) TEnum).

(* TODO:
  need the following test cases:
   - hwread
   - havocwrite

  and the following instrumentation:
   - all record states? (at end of execution)
   - optional: calc condition outcome

  *)



Definition run_db_op (rn : record_name) (op : micro) (dbs : database_state) :
        TraceM.M database_state :=
    match op with
    | MSetConst fn val =>
            do dbs' <- run_write_record_field dbs rn fn val;;
            ret dbs'
    | MCopy fn_src src_ty fn_dest dest_ty =>
            (* TODO: does this ever do a nontrivial conversion? *)
            do val <- run_read_record_field dbs rn fn_src;;
            do Hval_ty <- check_type (value_type val) src_ty;;
            do val' <- run_convert_value val dest_ty HNone;;
            do dbs' <- run_write_record_field dbs rn fn_dest val';;
            ret dbs'
    | MReadLink il il_ty fn f_ty =>
            do val <- run_read_record_field dbs (fl_rn il) (fl_fn il);;
            do Hval_ty <- check_type (value_type val) il_ty;;
            do val' <- run_convert_value val f_ty HReadLink;;
            do dbs' <- run_write_record_field dbs rn fn val';;
            do tval <- seek_take (fun evt =>
                    match evt with
                    | DbGetLinkValue v => Some v
                    | _ => None
                    end);;
            do Heq_val <- check_value val' tval;;
            ret dbs'
    | MWriteLink fn f_ty ol ol_ty =>
            do val <- run_read_record_field dbs rn fn;;
            do Hval_ty <- check_type (value_type val) f_ty;;
            do val' <- run_convert_value val ol_ty HWriteLink;;
            do dbs' <- run_write_record_field dbs (fl_rn ol) (fl_fn ol) val';;
            do tval <- seek_take (fun evt =>
                    match evt with
                    | DbPutLinkValue v => Some v
                    | _ => None
                    end);;
            do Heq_val <- check_value val' tval;;
            ret dbs'
    | MCalculate expr fn_out =>
            do f <- expect (expr.Dbl.denote expr)
                    (InvalidExpr expr);;
            do dbs' <- expect (run_calculate f fn_out dbs rn)
                    (OtherError "run_calculate failed");;
            ret dbs'
    | MHwRead fn f_ty =>
            do val <- seek_take (fun evt =>
                match evt with
                | DbHwRead v => Some v
                | _ => None
                end);;
            do Hval_ty <- check_type (value_type val) f_ty;;
            do dbs' <- run_write_record_field dbs rn fn val;;
            ret dbs'
    | MUnkRead fn f_ty =>
            do val <- seek_take (fun evt =>
                match evt with
                | DbGetLinkValue v => Some v
                | _ => None
                end);;
            do Hval_ty <- check_type (value_type val) f_ty;;
            do dbs' <- run_write_record_field dbs rn fn val;;
            ret dbs'
    | MUnkWrite =>
            ret dbs
    | MHavocUpdate =>
            do rs <- expect (lookup dbs rn)
                    (Impossible "missing record");;
            do rs' <- seek_take (fun evt =>
                match evt with
                | StrCalcResult rs => Some rs
                | _ => None
                end);;
            do Hrec_ty <- assert_eq (record_state_type rs') (record_state_type rs)
                    (OtherError "bad state type");;
            do dbs' <- expect (update_record (fun _ => Some rs') dbs rn)
                    (Impossible "update failed");;
            ret dbs'
    | MHavocWrite ol ol_ty =>
            do val <- seek_take (fun evt =>
                    match evt with
                    | DbPutLinkValue v => Some v
                    | _ => None
                    end);;
            do Hval_ty <- check_type (value_type val) ol_ty;;
            do dbs' <- run_write_record_field dbs (fl_rn ol) (fl_fn ol) val;;
            ret dbs'

    | _ => fail (Impossible "misclassified opcode in run_db_op")
    end.

Definition run_output_op (rn : record_name) (op : micro) (dbs : database_state) :
        TraceM.M output_event :=
    match op with
    | MHwWrite fn f_ty out_ty =>
            do val <- run_read_record_field dbs rn fn;;
            do Hval_ty <- check_type (value_type val) f_ty;;
            do val' <- run_convert_value val out_ty HNone;;
            ret (OHwWrite rn val')

    | MScheduleCallback delay code =>
            ret (OScheduleCallback delay rn code)

    | _ => fail (Impossible "misclassified opcode in run_output_op")
    end.

(* Given a state and a trace, interpret starting from the state, using the
   trace to pick the right values for unconstrained choices. *)
Definition run_step (dbp : database_program) (s : state) :
        TraceM.M (state * list output_event)  :=
    let dbs := state_dbs s in
    do frame <- expect (hd_error (state_stk s)) EmptyStack;;
    let frames := tl (state_stk s) in
    let rn := frame_rn frame in
    do rs <- expect (lookup dbs rn) (Impossible "bad record_name");;
    let rt := record_state_type rs in

    TraceM.context (WithCallStack (map frame_rn frames)) (
    TraceM.context (InRecord rt rn) (
    match frame_code frame with
    | [] => (* SPop *)
            TraceM.context (InPop rn) (
            do rs <- expect (lookup dbs rn)
                (Impossible "bad record_name in popped frame");;
            do rs' <- seek_take (fun evt =>
                match evt with
                | RecordEnd rn' rs' => if eq_dec rn rn' then Some rs' else None
                | _ => None
                end);;
            do Heq_rs <- assert_match rn rs rs';;
            ret (State dbs frames, [OTraceEnd rn rs])
            )
    | op :: ops =>
            TraceM.context (InOpcode op) (
            if is_db_op op then
                do dbs' <- run_db_op rn op dbs;;
                ret (State dbs' (Frame rn ops :: frames), [])
            else if is_output_op op then
                do oe <- run_output_op rn op dbs;;
                ret (State dbs (Frame rn ops :: frames), [oe])
            else match op with
            | MProcess fl =>
                    let rn' := rl_rn fl in
                    do rp <- expect (lookup dbp rn')
                            (Impossible "no program");;
                    do rs <- expect (lookup dbs rn')
                            (Impossible "no state");;
                    do rs' <- seek_take (fun evt =>
                        match evt with
                        | RecordBegin rn'' rs' => if eq_dec rn' rn'' then Some rs' else None
                        | _ => None
                        end);;
                    do Heq_rs <- assert_match rn' rs rs';;
                    let stk' := Frame rn' (rp_code rp) :: Frame rn ops :: frames in
                    ret (State dbs stk', [OTraceBegin rn' rs])

            | MCalcCond fn_cur fn_prev oopt body =>
                    do cur_val <- run_read_record_field dbs rn fn_cur;;
                    do cur <- run_unwrap_double cur_val;;
                    do prev_val <- run_read_record_field dbs rn fn_prev;;
                    do prev <- run_unwrap_double prev_val;;
                    if eval_calc_cond cur prev oopt then
                        ret (State dbs (Frame rn (body ++ ops) :: frames), [])
                    else
                        ret (State dbs (Frame rn ops :: frames), [])

            | MCheckPACT =>
                    do val <- run_read_record_field dbs rn f_PACT;;
                    do pact <- run_unwrap_enum val;;
                    if Z.eq_dec (enum_val pact) 0 then
                        ret (State dbs (Frame rn ops :: frames), [])
                    else
                        ret (State dbs (Frame rn [] :: frames), [])

            | MHavocProcess fl =>
                    (* TODO: seek_take RecordBegin (?) *)
                    do should_proc <- seek (fun evt => 
                        match evt with
                        | _ => None : option bool
                        end);;
                    if should_proc then
                        let rn' := rl_rn fl in
                        do rp <- expect (lookup dbp rn')
                                (Impossible "no program");;
                        do rs <- expect (lookup dbs rn')
                                (Impossible "no state");;
                        let stk' := Frame rn' (rp_code rp) :: Frame rn ops :: frames in
                        ret (State dbs stk', [OTraceBegin rn' rs])
                    else
                        ret (State dbs (Frame rn ops :: frames), [])

            | _ => fail (Impossible "misclassified opcode")
            end)
    end)).

Fixpoint run_star_step' (fuel : nat)  (dbp : database_program) (s : state) :
        TraceM.M (state * list output_event) :=
    match fuel with
    | 0 => fail OutOfFuel
    | S fuel =>
            match state_stk s with
            | [] => ret (s, [])
            | _ :: _ =>
                    do result1 <- run_step dbp s;;
                    let '(s1, oes1) := result1 in
                    do result2 <- run_star_step' fuel dbp s1;;
                    let '(s2, oes2) := result2 in
                    ret (s2, oes1 ++ oes2)
            end
    end.

Definition run_star_step (dbp : database_program) (s : state) :
        TraceM.M (state * list output_event) :=
    run_star_step' 10000 dbp s.

Definition null_dec {A} (xs : list A) : { xs = [] } + { xs <> [] }.
destruct xs; constructor; congruence.
Defined.

Definition run_event_loop_step (dbp : database_program)
        (dbs : database_state) (ie : input_event) :
        TraceM.M (database_state * list output_event) :=
    match ie with
    | IProcess rn =>
            do rp <- expect (lookup dbp rn) (Impossible "no program");;

            do rs <- expect (lookup dbs rn) (Impossible "no state");;
            do rs' <- seek_take (fun evt =>
                match evt with
                | RecordBegin rn' rs' => if eq_dec rn rn' then Some rs' else None
                | _ => None
                end);;
            do Heq_rs <- assert_match rn rs rs';;

            do result <- run_star_step dbp (State dbs [Frame rn (rp_code rp)]);;
            let '(State dbs' ops', oes) := result in
            do Hops' <- assert_sumbool (null_dec ops') (Impossible "run_star_step didn't finish");;
            ret (dbs', oes)
    | IRunCallback rn ops =>
            do rs <- expect (lookup dbs rn) (Impossible "no state");;
            do rs' <- seek_take (fun evt =>
                match evt with
                | RecordBegin rn' rs' => if eq_dec rn rn' then Some rs' else None
                | _ => None
                end);;
            do Heq_rs <- assert_match rn rs rs';;

            do result <- run_star_step dbp (State dbs [Frame rn ops]);;
            let '(State dbs' ops', oes) := result in
            do Hops' <- assert_sumbool (null_dec ops') (Impossible "run_star_step didn't finish");;
            ret (dbs', oes)
    end.

Fixpoint run_event_loop_star_step' (fuel : nat) (dbp : database_program)
        (dbs : database_state) (q : event_queue) :
        TraceM.M (database_state * list output_event) :=
    match fuel with
    | 0 => fail OutOfFuel
    | S fuel =>
            match q with
            | [] => ret (dbs, [])
            | (time, ie) :: q =>
                    do result1 <- run_event_loop_step dbp dbs ie;;
                    let '(dbs', oes1) := result1 in
                    let q' := handle_output_events time oes1 q in
                    do result2 <- run_event_loop_star_step' fuel dbp dbs' q';;
                    let '(dbs'', oes2) := result2 in
                    ret (dbs'', oes1 ++ oes2)
            end
    end.

Definition run_event_loop_star_step (dbp : database_program)
        (dbs : database_state) (q : event_queue) :
        TraceM.M (database_state * list output_event) :=
    run_event_loop_star_step' 1000 dbp dbs q.




(* Correctness proofs *)

(* For each function there are two proofs.
   (1) Soundness: if `run x` produces `x'`, then `R x x'`
   (2) Completeness: if `R x x'`, then there is some trace prefix `t0` such
       that `run x` produces `x'`, consuming `t0` from the front of the trace.
 *)

Lemma expect_sound : forall A (x : option A) err t x' t',
    expect x err t = inl (x', t') ->
    x = Some x'.
intros0 Hexpect.
unfold expect in Hexpect.
break_match; try discriminate.
unfold ret in Hexpect.
congruence.
Qed.

Lemma expect_complete : forall A x (x' : A) err t,
    x = Some x' ->
    expect x err t = inl (x', t).
intros. subst. simpl.  reflexivity.
Qed.


(* There's no lemma `assert_eq_sound`, because if `assert_eq ... = inl (H, t)`,
   `H` is already the proof of equality between `x` and `y`. *)

Lemma assert_eq_complete : forall (A : DecidableEquality) (x y : A) err t,
    x = y ->
    exists H, assert_eq x y err t = inl (H, t).
intros0 Heq.
unfold assert_eq, assert_sumbool.
break_match; try contradiction.
eexists; reflexivity.
Qed.


Ltac break_bind :=
    repeat lazymatch goal with
    | [ H : TraceM.bind _ _ _ = inl (_, _) |- _ ] =>
            eapply TraceM.break_bind in H;
            destruct H as (?x' & ?t' & ? & H)
    | [ H : TraceM.context _ _ _ = inl (_, _) |- _ ] =>
            eapply TraceM.context_inl in H
    end.


Lemma seek_sound : forall A f x t t',
    @seek A f t = inl (x, t') ->
    exists evt t0 t'',
        t = t0 ++ evt :: t'' /\
        t' = evt :: t'' /\
        f evt = Some x.
first_induction t; intros0 Hrun; simpl in Hrun.
{ discriminate. }
break_match.
- invc Hrun.
  eexists; exists []; eexists.
  split; [|split]; simpl; eauto.
- break_match; try discriminate.
  eapply IHt in Hrun as HH. destruct HH as (evt & t0 & t'' & ? & ? & ?).
  exists evt, (a :: t0), t''.
  split; [|split]; simpl; congruence.
Qed.

Lemma seek_take_sound : forall A f x t t',
    @seek_take A f t = inl (x, t') ->
    exists evt t0,
        t = t0 ++ evt :: t' /\
        f evt = Some x.
intros0 Hrun. unfold seek_take in Hrun.
break_bind.
on _, eapply_lem seek_sound. break_exists. break_and.
destruct t'0; try discriminate.
unfold TraceM.take in *. invc H1. invc H0. invc Hrun.
eexists; eexists; split; simpl; eauto.
Qed.



Lemma run_convert_value_exact_sound : forall val ty val',
    run_convert_value_exact val ty = Some val' ->
    convert_value val ty val'.
intros0 Hrun.
destruct val, ty; try discriminate; simpl in *.
all: repeat (break_match; try discriminate).

all: invc Hrun; split; [reflexivity|]; eauto.

- find_rewrite. intros. f_equal. f_equal. eapply proof_irrelevance.
- find_rewrite. intros. f_equal. f_equal. eapply proof_irrelevance.
- intros. f_equal. f_equal. eapply proof_irrelevance.
- intros. f_equal. f_equal. eapply proof_irrelevance.
Qed.

Lemma run_convert_value_exact_sound' : forall val ty,
    run_convert_value_exact val ty = None ->
    forall val', value_type val' = ty -> convert_value val ty val'.
intros0 Hrun.
destruct val, ty; try discriminate; simpl in *.
all: repeat (break_match; try discriminate).

all: intros0 Hty; split; [assumption|].
all: repeat find_rewrite.

all: intros; break_and; eauto; try contradiction; try congruence.
Qed.

Lemma run_convert_value_sound : forall val ty h val' t t',
    run_convert_value val ty h t = inl (val', t') ->
    convert_value val ty val'.
intros0 Hrun. unfold run_convert_value in Hrun.
break_match.

- invc Hrun. eapply run_convert_value_exact_sound. assumption.
- break_bind. invc Hrun.
  eapply run_convert_value_exact_sound'; eauto.
Qed.


Lemma hd_error_adjust : forall A l (x : A),
    hd_error l = Some x ->
    exists l', l = x :: l'.
intros0 Hhd.
exists (tl l).
unfold hd_error in *. break_match; try discriminate. simpl. congruence.
Qed.


Ltac hd_error_adjust :=
    repeat lazymatch goal with
    | [ H : hd_error (state_stk ?s) = Some ?x |- _ ] =>
            let x' := fresh "frame" in  (rename x into x' || set (x' := x));
            destruct (hd_error_adjust _ _ _ H) as [?frames ?];
            clear H

    | [ H : hd_error (frame_code ?f) = Some ?x |- _ ] =>
            let x' := fresh "op" in  (rename x into x' || set (x' := x));
            destruct (hd_error_adjust _ _ _ H) as [?ops ?];
            clear H

    | [ H : hd_error _ = Some ?x |- _ ] =>
            destruct (hd_error_adjust _ _ _ H) as [?xs ?];
            clear H

    end.



Lemma run_read_record_field_sound : forall dbs rn fn val t t',
    run_read_record_field dbs rn fn t = inl (val, t') ->
    read_record_field dbs rn fn = Some val.
intros0 Hrun. unfold run_read_record_field in Hrun.
eauto using expect_sound.
Qed.

Lemma run_write_record_field_sound : forall dbs rn fn val dbs' t t',
    run_write_record_field dbs rn fn val t = inl (dbs', t') ->
    write_record_field dbs rn fn val = Some dbs'.
intros0 Hrun. unfold run_write_record_field in Hrun.
eauto using expect_sound.
Qed.

Lemma run_unwrap_double_sound' : forall v x t t',
    run_unwrap_double v t = inl (x, t') ->
    v = VDouble x.
intros0 Hrun.
eapply expect_sound in Hrun.
destruct v; try discriminate. simpl in *. congruence.
Qed.

Lemma run_unwrap_enum_sound : forall v x t t',
    run_unwrap_enum v t = inl (x, t') ->
    unwrap_enum v = Some x.
intros0 Hrun.  eapply expect_sound in Hrun.  assumption.
Qed.



Lemma run_db_op_sound : forall rn op dbs dbs' t t',
    run_db_op rn op dbs t = inl (dbs', t') ->
    db_step rn op dbs dbs'.
intros0 Hrun.  unfold run_db_op in Hrun.
break_match; try discriminate.

- (* MSetConst *)
  break_bind. invc Hrun. eapply SSetConst.
  + eapply run_write_record_field_sound. eassumption.

- (* MCopy *)
  break_bind. invc Hrun. eapply SCopy.
  + eapply run_read_record_field_sound. eassumption.
  + reflexivity.
  + eapply run_convert_value_sound. eassumption.
  + eapply run_write_record_field_sound. eassumption.

- (* MReadLink *)
  break_bind. invc Hrun. eapply SReadLink.
  + eapply run_read_record_field_sound. eassumption.
  + reflexivity.
  + eapply run_convert_value_sound. eassumption.
  + eapply run_write_record_field_sound. eassumption.

- (* MWriteLink *)
  break_bind. invc Hrun. eapply SWriteLink.
  + eapply run_read_record_field_sound. eassumption.
  + reflexivity.
  + eapply run_convert_value_sound. eassumption.
  + eapply run_write_record_field_sound. eassumption.

- (* MCalculate *)
  break_bind. invc Hrun. eapply SCalculate.
  + eapply expect_sound. eassumption.
  + eapply expect_sound. eassumption.

- (* MHwRead *)
  break_bind. invc Hrun. eapply SHwRead.
  + reflexivity.
  + eapply run_write_record_field_sound. eassumption.

- (* MUnkRead *)
  break_bind. invc Hrun. eapply SUnkRead.
  + reflexivity.
  + eapply run_write_record_field_sound. eassumption.

- (* MUnkWrite *)
  break_bind. invc Hrun. eapply SUnkWrite.

- (* MHavocUpdate *)
  break_bind. invc Hrun. eapply SHavocUpdate.
  + eapply expect_sound. eassumption.
  + eassumption.
  + eapply expect_sound. eassumption.

- (* MHavocWrite *)
  break_bind. invc Hrun. eapply SHavocWrite.
  + reflexivity.
  + eapply run_write_record_field_sound. eassumption.

Qed.


Lemma run_output_op_sound : forall rn op dbs oe t t',
    run_output_op rn op dbs t = inl (oe, t') ->
    output_step rn op dbs oe.
intros0 Hrun.
unfold run_output_op in Hrun.
break_match; try discriminate.

- break_bind. invc Hrun. eapply SHwWrite.
  + eapply expect_sound. eassumption.
  + reflexivity.
  + eapply run_convert_value_sound. eassumption.

- break_bind. invc Hrun. eapply SScheduleCallback.

Qed.

Ltac simplM :=
    let g := fresh "g" in
    let x := fresh "x" in
    simpl; change (TraceM.bind (TraceM.ret ?x) ?g) with (g x); cbv beta.

(*
Lemma run_output_op_complete : forall rn op dbs oe t,
    output_step rn op dbs oe ->
    exists t0, run_output_op rn op dbs t = inl (oe, t0 ++ t).
intros0 Hstep. invc Hstep.

- simpl.  unfold TraceM.bind.
  erewrite expect_complete by eauto.
  forward eapply assert_eq_complete; try reflexivity.  break_exists.
    on (assert_eq _ _ _ _ = _), fun H => rewrite H.
  erewrite run_convert_value_complete by eauto.
  exists []. reflexivity.

- simpl.
  exists []. reflexivity.
Qed.
*)


Lemma run_step_sound : forall dbp s s' oes t t',
    run_step dbp s t = inl ((s', oes), t') ->
    step dbp s s' oes.
intros0 Hrun.  unfold run_step in Hrun.
break_bind.
do 2 on _, eapply_lem expect_sound. hd_error_adjust.
destruct s, frame; simpl in *; subst.
break_match; try discriminate.

{ (* pop case *)
  break_bind. invc Hrun. eapply SPop.
  + eapply expect_sound. eassumption. }

break_bind. break_match.

{ (* db step case *)
  subst. break_bind. invc Hrun.  eapply SDb.
  + eapply run_db_op_sound. eassumption. }

break_match.

{ (* output step case *)
  subst. break_bind. invc Hrun.  eapply SOutput.
  + eapply run_output_op_sound. eassumption. }

break_match; try discriminate.

- (* Process *)
  subst. break_bind. invc Hrun. eapply SProcess.
  + eapply expect_sound. eassumption.
  + eapply expect_sound. eassumption.

- (* CalcCond *)
  subst. break_bind. break_match; invc Hrun.
  + eapply SCalcCondYes.
    * eapply run_read_record_field_sound. eassumption.
    * eapply run_unwrap_double_sound'. eassumption.
    * eapply run_read_record_field_sound. eassumption.
    * eapply run_unwrap_double_sound'. eassumption.
    * assumption.
  + eapply SCalcCondNo.
    * eapply run_read_record_field_sound. eassumption.
    * eapply run_unwrap_double_sound'. eassumption.
    * eapply run_read_record_field_sound. eassumption.
    * eapply run_unwrap_double_sound'. eassumption.
    * assumption.

- (* CheckPACT *)
  subst. break_bind. break_match; invc Hrun.
  + eapply SCheckPACTZero.
    * eapply run_read_record_field_sound. eassumption.
    * eapply run_unwrap_enum_sound. eassumption.
    * assumption.
  + eapply SCheckPACTNonZero.
    * eapply run_read_record_field_sound. eassumption.
    * eapply run_unwrap_enum_sound. eassumption.
    * assumption.

- (* HavocProcess *)
  subst. break_bind. break_match.
  + break_bind. invc Hrun.  eapply SHavocProcessYes.
    * eapply expect_sound. eassumption.
    * eapply expect_sound. eassumption.
  + invc Hrun.  eapply SHavocProcessNo.
Qed.


Lemma run_star_step'_sound : forall fuel dbp s s' oes t t',
    run_star_step' fuel dbp s t = inl ((s', oes), t') ->
    star_step dbp s s' oes /\ state_stk s' = [].
induction fuel; intros0 Hrun; try discriminate. simpl in Hrun.
break_match.

{ (* nil case *)
  invc Hrun. split; eauto. constructor. }

break_bind. break_match. break_bind. break_match.
invc Hrun.
forward eapply run_step_sound; eauto.
forward eapply IHfuel; eauto. break_and.
split; eauto. econstructor; eassumption.
Qed.

Lemma run_star_step_sound : forall dbp s s' oes t t',
    run_star_step dbp s t = inl ((s', oes), t') ->
    star_step dbp s s' oes /\ state_stk s' = [].
(* We get timeouts / stack overflow if this proof is not built just so... *)
exact (run_star_step'_sound 10000).
Qed.

(*
Lemma run_event_loop_step_sound : forall dbp dbs ie dbs' oes t t',
    run_event_loop_step dbp dbs ie t = inl ((dbs', oes), t') ->
    event_loop_step dbp dbs ie dbs' oes.
intros0 Hrun.  unfold run_event_loop_step in Hrun.
repeat (break_match || break_bind); subst.

- invc Hrun. econstructor.
  + eapply expect_sound. eassumption.
  + eapply run_star_step_sound. eassumption.

- invc Hrun. econstructor.
  + eapply run_star_step_sound. eassumption.
Qed.

Lemma run_event_loop_star_step'_sound : forall fuel dbp dbs q dbs' oes t t',
    run_event_loop_star_step' fuel dbp dbs q t = inl ((dbs', oes), t') ->
    event_loop_star_step dbp dbs q dbs' oes.
induction fuel; intros0 Hrun; try discriminate. simpl in Hrun.
break_match.

{ (* nil case *)
  invc Hrun. constructor. }

break_match. break_bind. break_match. break_bind. break_match.
invc Hrun.
econstructor.
- eapply run_event_loop_step_sound. eassumption.
- eapply IHfuel. eassumption.
Qed.

Lemma run_event_loop_star_step_sound : forall dbp dbs q dbs' oes t t',
    run_event_loop_star_step dbp dbs q t = inl ((dbs', oes), t') ->
    event_loop_star_step dbp dbs q dbs' oes.
exact (run_event_loop_star_step'_sound 1000).
Qed.
*)


(* Entry point *)

Definition validate_trace_event_loop
        (dbp : database_program) (dbs : database_state) (q : event_queue)
        (t : trace) : (database_state * list output_event) + error :=
    match run_event_loop_star_step dbp dbs q t with
    | inl ((s', oes), t') =>
            match t' with
            | [] =>  inl (s', oes)
            | _ :: _ => inr (UnusedEvents (length t'))
            end
    | inr e => inr e
    end.

(*
Lemma validate_trace_event_loop_sound : forall dbp dbs q t dbs' oes,
    validate_trace_event_loop dbp dbs q t = inl (dbs', oes) ->
    event_loop_star_step dbp dbs q dbs' oes.
intros0 Hrun. unfold validate_trace_event_loop in Hrun.
break_match; try discriminate. break_match. break_match.
break_match; try discriminate.
invc Hrun. eapply run_event_loop_star_step_sound. eassumption.
Qed.
*)



(* old entry points... *)

Definition run_record_star_step (dbp : database_program) (dbs : database_state) (rn : record_name) :
        TraceM.M (database_state * list output_event) :=
    do rp <- expect (lookup dbp rn)
            (OtherError "bad record name");;

    do rs <- expect (lookup dbs rn)
            (Impossible "no state");;
    do rs' <- seek_take (fun evt =>
        match evt with
        | RecordBegin rn' rs' => if eq_dec rn rn' then Some rs' else None
        | _ => None
        end);;
    do Heq_rs <- assert_match rn rs rs';;

    let frame := Frame rn (rp_code rp) in
    let s := State dbs [frame] in
    do result <- run_star_step dbp s;;
    let '(s', oes) := result in
    ret (state_dbs s', oes).

Definition record_star_step dbp dbs rn dbs' oes :=
    exists rp,
        lookup dbp rn = Some rp /\
        star_step dbp (State dbs [Frame rn (rp_code rp)]) (State dbs' []) oes.

Lemma run_record_star_step_sound : forall dbp dbs rn dbs' oes t t',
    run_record_star_step dbp dbs rn t = inl ((dbs', oes), t') ->
    record_star_step dbp dbs rn dbs' oes.
intros0 Hrun. unfold run_record_star_step in Hrun.
break_bind. break_match. invc Hrun.
eexists.
split.
- eapply expect_sound. eassumption.
- forward eapply run_star_step_sound; eauto.  break_and.
  destruct s; simpl in *; subst.
  assumption.
Qed.


Definition validate_trace (dbp : database_program) (dbs : database_state) (rn : record_name)
        (t : trace) : (database_state * list output_event) + error :=
    match run_record_star_step dbp dbs rn t with
    | inl ((s', oes), t') => inl (s', oes)
    | inr e => inr e
    end.

Lemma validate_trace_sound : forall dbp dbs rn t dbs' oes,
    validate_trace dbp dbs rn t = inl (dbs', oes) ->
    record_star_step dbp dbs rn dbs' oes.
intros0 Hrun. unfold validate_trace in Hrun.
break_match; try discriminate. break_match. break_match.
invc Hrun. eapply run_record_star_step_sound. eassumption.
Qed.


Inductive multi_record_star_step (dbp : database_program) :
        database_state -> list record_name -> database_state -> list output_event -> Prop :=
| MrssNil : forall dbs, multi_record_star_step dbp dbs [] dbs []
| MrssCons : forall dbs dbs' dbs'' rn rns oes1 oes2 oes12,
        record_star_step dbp dbs rn dbs' oes1 ->
        multi_record_star_step dbp dbs' rns dbs'' oes2 ->
        oes12 = oes1 ++ oes2 ->
        multi_record_star_step dbp dbs (rn :: rns) dbs'' oes12.

Fixpoint validate_trace_multi_record
        (dbp : database_program) (dbs : database_state) (rns : list record_name)
        (t : trace) : (database_state * list output_event) + error :=
    match rns with
    | [] => inl (dbs, [])
    | rn :: rns =>
            match run_record_star_step dbp dbs rn t with
            | inl ((dbs', oes1), t') =>
                    match validate_trace_multi_record dbp dbs' rns t' with
                    | inl (dbs'', oes2) => inl (dbs'', oes1 ++ oes2)
                    | inr e => inr e
                    end
            | inr e => inr e
            end
    end.

Lemma validate_trace_multi_record_sound : forall dbp dbs rns t dbs'' oes12,
    validate_trace_multi_record dbp dbs rns t = inl (dbs'', oes12) ->
    multi_record_star_step dbp dbs rns dbs'' oes12.
first_induction rns; intros0 Hrun.

{ simpl in Hrun. invc Hrun. econstructor. }

simpl in Hrun.
break_match; try discriminate.  destruct p as [[dbs' oes1] t'].
break_match; try discriminate.  destruct p as [dbs''2 oes2].
invc Hrun.
on _, eapply_lem run_record_star_step_sound.
econstructor; eauto.
Qed.


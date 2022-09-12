Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Omega.
Require Import String.

Require Import v1.NeutronTactics.
Require Import v1.Util.
Require Import v1.Multi.
Require Import v1.MultiAux.

Require Import epics.SpecTypes.
Require Import epics.SpecRecords.
Require Import epics.Opcodes.
Require Import epics.SpecStep.
Require expr.Dbl.
Require Import util.ListLemmas.

Set Default Timeout 10.

Local Open Scope string.


Inductive record_has_field : record_type -> field_name -> field_type -> Prop :=
| RecordHasField : forall rt fn ft,
        record_field_type rt fn = Some ft ->
        record_has_field rt fn ft.

Definition all_fields : list field_name :=
    map f_A_to_L (index_list 12) ++
    map f_AA_to_LL (index_list 12) ++
    map f_DO1_to_DOA (index_list 10) ++
    [ f_VAL; f_PVAL; f_OVAL
    ; f_SVAL; f_OSV
    ; f_AVAL; f_OAV
    ; f_PACT
    ; f_tmp0 ].

Lemma A_to_L_in_all_fields : forall i,
    In (f_A_to_L i) all_fields.
intros.
unfold all_fields. repeat rewrite in_app_iff.
left. eapply in_map. eapply index_list_in.
Qed.

Lemma AA_to_LL_in_all_fields : forall i,
    In (f_AA_to_LL i) all_fields.
intros.
unfold all_fields. repeat rewrite in_app_iff.
right. left. eapply in_map. eapply index_list_in.
Qed.

Lemma DO1_to_DOA_in_all_fields : forall i,
    In (f_DO1_to_DOA i) all_fields.
intros.
unfold all_fields. repeat rewrite in_app_iff.
do 2 right. left. eapply in_map. eapply index_list_in.
Qed.

Lemma in_all_fields : forall rt fn ty,
    record_has_field rt fn ty ->
    In fn all_fields.
inversion 1; subst. destruct rt, fn.
all: unfold record_field_type in *.
all: try discriminate H0.

all: try solve [eauto using
    A_to_L_in_all_fields,
    AA_to_LL_in_all_fields,
    DO1_to_DOA_in_all_fields
].
all: unfold all_fields; repeat rewrite in_app_iff; do 3 right.
all: simpl.
all: eauto 999.
Qed.


Inductive wfm_field_access dbt : record_name -> field_name -> field_type -> Prop :=
| WfmFieldAccess : forall rn fn ty,
        forall rt, lookup_type dbt rn = Some rt ->
        record_has_field rt fn ty ->
        wfm_field_access dbt rn fn ty.

Inductive wfm_field_link dbt : field_link -> field_type -> Prop :=
| WfmFieldLink : forall fl ty,
        wfm_field_access dbt (fl_rn fl) (fl_fn fl) ty ->
        wfm_field_link dbt fl ty.

Inductive wfm_record_link dbt : record_link -> Prop :=
| WfmRecordLink : forall rl,
        forall ft, lookup_type dbt (rl_rn rl) = Some ft ->
        wfm_record_link dbt rl.

Inductive wfm_calculate : record_type -> field_name -> Prop :=
| WfmCalculate : forall rt fn_out,
        (rt = RtCalc \/ rt = RtCalcOut) ->
        (fn_out = f_VAL \/ fn_out = f_OVAL) ->
        (forall i, record_has_field rt (f_A_to_L i) TDouble) ->
        record_has_field rt fn_out TDouble ->
        wfm_calculate rt fn_out.

(*
Inductive wfm_calculate_str : record_type -> field_name -> field_name -> Prop :=
| WfmCalculateStr : forall rt fn_out_dbl fn_out_str,
        rt = RtStrCalcOut ->
        (forall i, record_has_field rt (f_A_to_L i) TDouble) ->
        (forall i, record_has_field rt (f_AA_to_LL i) TString) ->
        record_has_field rt fn_out_dbl TDouble ->
        record_has_field rt fn_out_str TString ->
        wfm_calculate_str rt fn_out_dbl fn_out_str.
*)

Inductive wfm_instr dbt : record_type -> micro -> Prop :=
| WfmiSetConst : forall rt fn val,
        record_has_field rt fn (value_type val) ->
        wfm_instr dbt rt (MSetConst fn val)
| WfmiCopy : forall rt fn_src src_ty fn_dest dest_ty,
        record_has_field rt fn_src src_ty ->
        record_has_field rt fn_dest dest_ty ->
        wfm_instr dbt rt (MCopy fn_src src_ty fn_dest dest_ty)
| WfmiReadLink : forall rt il il_ty fn f_ty,
        wfm_field_link dbt il il_ty ->
        record_has_field rt fn f_ty ->
        wfm_instr dbt rt (MReadLink il il_ty fn f_ty)
| WfmiWriteLink : forall rt fn f_ty ol ol_ty,
        record_has_field rt fn f_ty ->
        wfm_field_link dbt ol ol_ty ->
        wfm_instr dbt rt (MWriteLink fn f_ty ol ol_ty)
| WfmiProcess : forall rt fl,
        wfm_record_link dbt fl ->
        wfm_instr dbt rt (MProcess fl)
| WfmiCalculate : forall rt expr fn_out,
        (exists f, expr.Dbl.denote expr = Some f) ->
        wfm_calculate rt fn_out ->
        wfm_instr dbt rt (MCalculate expr fn_out)
        (*
| WfmiCalculateStr : forall rt expr fn_out_dbl fn_out_str,
        (expr.DblStr.well_typed expr.DblStr.Dbl expr \/
         expr.DblStr.well_typed expr.DblStr.Str expr) ->
        wfm_calculate_str rt fn_out_dbl fn_out_str ->
        wfm_instr dbt rt (MCalculateStr expr fn_out_dbl fn_out_str)
        *)
| WfmiHwRead : forall rt fn f_ty,
        record_has_field rt fn f_ty ->
        wfm_instr dbt rt (MHwRead fn f_ty)
| WfmiHwWrite : forall rt fn f_ty out_ty,
        record_has_field rt fn f_ty ->
        wfm_instr dbt rt (MHwWrite fn f_ty out_ty)
| WfmiCalcCond : forall rt fn_cur fn_prev oopt body,
        record_has_field rt fn_cur TDouble ->
        record_has_field rt fn_prev TDouble ->
        Forall (wfm_instr dbt rt) body ->
        wfm_instr dbt rt (MCalcCond fn_cur fn_prev oopt body)
| WfmiScheduleCallback : forall rt delay code,
        Forall (wfm_instr dbt rt) code ->
        wfm_instr dbt rt (MScheduleCallback delay code)
| WfmiCheckPACT : forall rt,
        record_has_field rt f_PACT TEnum ->
        wfm_instr dbt rt MCheckPACT
| WfmUnkRead : forall rt fn f_ty,
        record_has_field rt fn f_ty ->
        wfm_instr dbt rt (MUnkRead fn f_ty)
| WfmUnkWrite : forall rt,
        wfm_instr dbt rt (MUnkWrite)
| WfmiHavocUpdate : forall rt,
        wfm_instr dbt rt (MHavocUpdate)
| WfmiHavocWrite : forall rt ol ol_ty,
        wfm_field_link dbt ol ol_ty ->
        wfm_instr dbt rt (MHavocWrite ol ol_ty)
| WfmiHavocProcess : forall rt fl,
        wfm_record_link dbt fl ->
        wfm_instr dbt rt (MHavocProcess fl)
.

Definition wfm_record dbt rp :=
    Forall (wfm_instr dbt (rp_type rp)) (rp_code rp).

Definition wfm_database dbt dbp :=
    Forall (wfm_record dbt) dbp.

Inductive wfm_frame dbt : frame -> Prop :=
| WfmFrame : forall frame rt,
        lookup dbt (frame_rn frame) = Some rt ->
        Forall (wfm_instr dbt rt) (frame_code frame) ->
        wfm_frame dbt frame.

Definition wfm_state dbt state :=
    Forall (wfm_frame dbt) (state_stk state).

Inductive wfm_input_event dbt : input_event -> Prop :=
| WfieProcess : forall rn,
        forall rt, lookup_type dbt rn = Some rt ->
        wfm_input_event dbt (IProcess rn)
| WfieRunCallback : forall rn ops,
        forall rt, lookup_type dbt rn = Some rt ->
        Forall (wfm_instr dbt rt) ops ->
        wfm_input_event dbt (IRunCallback rn ops)
.

Inductive wfm_output_event dbt : output_event -> Prop :=
| WfoeTraceInput : forall ie,
        wfm_input_event dbt ie ->
        wfm_output_event dbt (OTraceInput ie)
| WfoeTraceBegin : forall rn rs,
        forall rt, lookup_type dbt rn = Some rt ->
        wfm_output_event dbt (OTraceBegin rn rs)
| WfoeTraceEnd : forall rn rs,
        forall rt, lookup_type dbt rn = Some rt ->
        wfm_output_event dbt (OTraceEnd rn rs)
| WfoeHwWrite : forall rn val,
        forall rt, lookup_type dbt rn = Some rt ->
        wfm_output_event dbt (OHwWrite rn val)
| WfoeScheduleCallback : forall delay rn ops,
        forall rt, lookup_type dbt rn = Some rt ->
        Forall (wfm_instr dbt rt) ops ->
        wfm_output_event dbt (OScheduleCallback delay rn ops)
.



(* wfm proofs *)

Inductive wf_error_context :=
| CtxRecord (rn : record_name)
| CtxOpcode (op : micro)
| CtxField (fn : field_name)
| CtxTargetRecord (rn : record_name)
.

Inductive wf_error :=
| WfeNoSuchRecord (rn : record_name)
| WfeNoSuchField (rt : record_type) (fn : field_name)
| WfeWrongFieldType (rt : record_type) (fn : field_name) (ft : field_type) (ft' : field_type)
| WfeNotConvertible (ty1 ty2 : field_type)
| WfeMultipleErrors (first : wf_error) (rest : wf_error)
| WfeInContext (ctx : wf_error_context) (e : wf_error)
| WfeWrongRecordType (actual : record_type) (expected : list record_type)
| WfeWrongFieldName (actual : field_name) (expected : list field_name)
| WfeBadExpr
.

Lemma record_has_field_A2L_eq : forall rt ty i j,
    index_nat i = index_nat j ->
    record_has_field rt (f_A_to_L i) ty ->
    record_has_field rt (f_A_to_L j) ty.
intros0 Heq Hf.
invc Hf. destruct rt; try discriminate.
all: econstructor; eauto.
Qed.

Lemma record_has_field_A2L_irrel : forall rt ty i pf1 pf2,
    record_has_field rt (f_A_to_L (Index i pf1)) ty ->
    record_has_field rt (f_A_to_L (Index i pf2)) ty.
intros0 HH. invc HH.
destruct rt; try discriminate.
all: econstructor; eauto.
Qed.

Lemma record_has_field_AA2LL_irrel : forall rt ty i pf1 pf2,
    record_has_field rt (f_AA_to_LL (Index i pf1)) ty ->
    record_has_field rt (f_AA_to_LL (Index i pf2)) ty.
intros0 HH. invc HH.
destruct rt; try discriminate.
all: econstructor; eauto.
Qed.

Ltac die e := right; exact e.
Ltac die_auto := right; assumption.
Ltac die_ctx ctx := right; apply (WfeInContext ctx); assumption.
Ltac die_auto_ctx := right; apply WfeInContext; assumption.

Definition check_record_has_field rt fn ft : record_has_field rt fn ft + wf_error.
destruct (record_field_type rt fn) as [ft' | ] eqn:?.
- destruct (field_type_eq_dec ft ft').
  + left. subst. constructor. auto.
  + die (WfeWrongFieldType rt fn ft ft').
- die (WfeNoSuchField rt fn).
Defined.

Definition check_wfm_field_access dbt rn fn ft : wfm_field_access dbt rn fn ft + wf_error.
destruct (lookup_type dbt rn) as [ rt | ] eqn:?; [ | die (WfeNoSuchRecord rn) ].
destruct (check_record_has_field rt fn ft); [ | die_ctx (CtxTargetRecord rn) ].
left. econstructor; eassumption.
Defined.

Definition check_wfm_field_link dbt fl ft : wfm_field_link dbt fl ft + wf_error.
destruct (check_wfm_field_access dbt (fl_rn fl) (fl_fn fl) ft); [ | die_auto ].
left. econstructor; eassumption.
Defined.

Definition check_wfm_record_link dbt rl : wfm_record_link dbt rl + wf_error.
destruct (lookup_type dbt (rl_rn rl)) eqn:?; [ | die (WfeNoSuchRecord (rl_rn rl)) ].
left. econstructor; eassumption.
Defined.

Definition check_wfm_calculate_record_type rt :
    (rt = RtCalc \/ rt = RtCalcOut) + wf_error.
destruct rt eqn:?;
first [ left; solve [eauto] | die (WfeWrongRecordType rt [RtCalc; RtCalcOut]) ].
Defined.

Definition check_wfm_calculate_field_name fn_out :
    (fn_out = f_VAL \/ fn_out = f_OVAL) + wf_error.
destruct fn_out eqn:?;
first [ left; solve [eauto] | die (WfeWrongFieldName fn_out [f_VAL; f_OVAL]) ].
Defined.

Definition check_wfm_calculate rt fn_out : wfm_calculate rt fn_out + wf_error.
destruct (check_wfm_calculate_record_type rt); [ | die_auto ].
destruct (check_wfm_calculate_field_name fn_out); [ | die_auto ].
let do_slot n :=
    let fn := constr:(f_A_to_L ltac:(mk_index n)) in
    destruct (check_record_has_field rt fn TDouble);
    [ | die_ctx (CtxField fn) ] in
do_slot  0;
do_slot  1;
do_slot  2;
do_slot  3;
do_slot  4;
do_slot  5;
do_slot  6;
do_slot  7;
do_slot  8;
do_slot  9;
do_slot 10;
do_slot 11.
destruct (check_record_has_field rt fn_out TDouble); [ | die_auto ].

left. econstructor; eauto.
intro i. destruct i as [ i Hlt ].
repeat (destruct i; try omega); eauto using record_has_field_A2L_irrel.
Defined.

(*
Definition check_wfm_calculate_str_record_type rt :
    (rt = RtStrCalcOut) + wf_error.
destruct rt eqn:?;
first [ left; solve [eauto] | die (WfeWrongRecordType rt [RtStrCalcOut]) ].
Defined.

Definition check_wfm_calculate_str rt fn_out_dbl fn_out_str :
    wfm_calculate_str rt fn_out_dbl fn_out_str + wf_error.
destruct (check_wfm_calculate_str_record_type rt); [ | die_auto ].

let do_slot n :=
    let fn := constr:(f_A_to_L ltac:(mk_index n)) in
    destruct (check_record_has_field rt fn TDouble);
    [ | die_ctx (CtxField fn) ] in
do_slot  0;
do_slot  1;
do_slot  2;
do_slot  3;
do_slot  4;
do_slot  5;
do_slot  6;
do_slot  7;
do_slot  8;
do_slot  9;
do_slot 10;
do_slot 11.

let do_slot n :=
    let fn := constr:(f_AA_to_LL ltac:(mk_index n)) in
    destruct (check_record_has_field rt fn TString);
    [ | die_ctx (CtxField fn) ] in
do_slot  0;
do_slot  1;
do_slot  2;
do_slot  3;
do_slot  4;
do_slot  5;
do_slot  6;
do_slot  7;
do_slot  8;
do_slot  9;
do_slot 10;
do_slot 11.

destruct (check_record_has_field rt fn_out_dbl TDouble); [ | die_auto ].
destruct (check_record_has_field rt fn_out_str TString); [ | die_auto ].

left. econstructor; eauto.
- intro i. destruct i as [ i Hlt ].
  repeat (destruct i; try omega); eauto using record_has_field_A2L_irrel.
- intro i. destruct i as [ i Hlt ].
  repeat (destruct i; try omega); eauto using record_has_field_AA2LL_irrel.
Defined.
*)

Definition check_wfm_instr dbt rt : forall op, wfm_instr dbt rt op + wf_error.
intro op. pose proof (CtxOpcode op) as ctx.
induction op using micro_rect_mut
    with (Pl := fun ops => (Forall (wfm_instr dbt rt) ops + wf_error)%type).

- (* MSetConst *)
  destruct (check_record_has_field rt fn (value_type val)); [ | die_auto_ctx ].
  left. econstructor; eassumption.

- (* MCopy *)
  destruct (check_record_has_field rt fn_src src_ty); [ | die_auto_ctx ].
  destruct (check_record_has_field rt fn_dest dest_ty); [ | die_auto_ctx ].
  left. econstructor; eassumption.

- (* MReadLink *)
  destruct (check_wfm_field_link dbt il il_ty); [ | die_auto_ctx ].
  destruct (check_record_has_field rt fn f_ty); [ | die_auto_ctx ].
  left. econstructor; eassumption.

- (* MWriteLink *)
  destruct (check_record_has_field rt fn f_ty); [ | die_auto_ctx ].
  destruct (check_wfm_field_link dbt ol ol_ty); [ | die_auto_ctx ].
  left. econstructor; eassumption.

- (* MProcess *)
  destruct (check_wfm_record_link dbt fl); [ | die_auto_ctx ].
  left. econstructor; eassumption.

- (* MCalculate *)
  destruct (expr.Dbl.denote expr) eqn:?; [ | die WfeBadExpr ].
  destruct (check_wfm_calculate rt fn_out); [ | die_auto_ctx ].
  left. econstructor; eauto.

(*
- (* MCalculateStr *)
  (* TODO: do something useful with the error message from expr.DblStr.typecheck *)
  destruct (expr.DblStr.typecheck_expr _ expr); [ | die WfeBadExpr ].
  destruct (check_wfm_calculate_str rt fn_out_dbl fn_out_str); [ | die_auto_ctx ].
  left. econstructor; eassumption.
*)

- (* MHwRead *)
  destruct (check_record_has_field rt fn f_ty); [ | die_auto_ctx ].
  left. econstructor; eassumption.

- (* MHwWrite *)
  destruct (check_record_has_field rt fn f_ty); [ | die_auto_ctx ].
  left. econstructor; eassumption.

- (* MCalcCond *)
  destruct (check_record_has_field rt fn_cur TDouble); [ | die_auto_ctx ].
  destruct (check_record_has_field rt fn_prev TDouble); [ | die_auto_ctx ].
  destruct (IHop); [ | die_auto_ctx ].
  left. econstructor; eassumption.

- (* MScheduleCallback *)
  destruct (IHop); [ | die_auto_ctx ].
  left. econstructor; eassumption.

- (* MCheckPACT *)
  destruct (check_record_has_field rt f_PACT TEnum); [ | die_auto_ctx ].
  left. econstructor; eassumption.

- (* MUnkRead *)
  destruct (check_record_has_field rt fn f_ty); [ | die_auto_ctx ].
  left. econstructor; eassumption.

- (* MUnkWrite *)
  left. econstructor; eassumption.

- (* MHavocUpdate *)
  left. econstructor; eassumption.

- (* MHavocWrite *)
  destruct (check_wfm_field_link dbt ol ol_ty); [ | die_auto_ctx ].
  left. econstructor; eassumption.

- (* MHavocProcess *)
  destruct (check_wfm_record_link dbt fl); [ | die_auto_ctx ].
  left. econstructor; eassumption.


- (* nil *)
  left. constructor.

- (* cons *)
  destruct IHop as [ ? | e1 ], IHop0 as [ ? | e2 ].
  1: left; econstructor; eassumption.
  all: first [ die (WfeMultipleErrors e1 e2) | die_auto ].

Defined.

Definition check_list {A} {P : A -> Prop} (xs : list A)
    (check_one : forall x, P x + wf_error) :
    Forall P xs + wf_error.
induction xs as [ | x xs ].
- left. constructor.
- destruct (check_one x) as [? | e1];
  destruct IHxs as [? | e2].
  1: left; econstructor; eassumption.
  all: first [ die (WfeMultipleErrors e1 e2) | die_auto ].
Defined.

Definition check_record_list {A} {P : A -> Prop} (xs : list A)
    (check_one : forall x, P x + wf_error) :
    Forall P xs + wf_error.
refine (
    let check_numbered (p : nat * A) : P (snd p) + wf_error :=
        let '(n, r) := p in
        match check_one r with
        | inl pf => inl pf
        | inr err => inr (WfeInContext (CtxRecord n) err)
        end in _
).
clearbody check_numbered.

destruct (check_list (numbered xs) check_numbered); [ | die_auto ].
left. rewrite <- numbered_map_snd. rewrite <- Forall_map. assumption.
Qed.

Definition check_wfm_record dbt rp : wfm_record dbt rp + wf_error :=
    check_list (rp_code rp) (check_wfm_instr dbt (rp_type rp)).

Definition check_wfm_database dbt dbp : wfm_database dbt dbp + wf_error :=
    check_record_list dbp (check_wfm_record dbt).

Definition check_wfm_frame dbt frame : wfm_frame dbt frame + wf_error.
destruct (lookup dbt (frame_rn frame)) as [ rt | ] eqn:?;
        [ | die (WfeNoSuchRecord (frame_rn frame)) ].
destruct (check_list (frame_code frame) (check_wfm_instr dbt rt));
        [ | die_auto ].
left. econstructor; eassumption.
Defined.

Definition check_wfm_state dbt state : wfm_state dbt state + wf_error :=
    check_list (state_stk state) (check_wfm_frame dbt).

Definition check_wfm_input_event dbt ie : wfm_input_event dbt ie + wf_error.
destruct ie.

- (* IProcess *)
  destruct (lookup_type dbt rn) eqn:?; [ | die (WfeNoSuchRecord rn) ].
  left. econstructor; eassumption.

- (* IRunCallback *)
  destruct (lookup_type dbt rn) as [ rt | ] eqn:?; [ | die (WfeNoSuchRecord rn) ].
  destruct (@check_list _ _ ops (check_wfm_instr dbt rt)); [ | die_auto ].
  left. econstructor; eassumption.

Defined.

Definition check_wfm_input_events dbt ies : Forall (wfm_input_event dbt) ies + wf_error.
eapply check_list.
eapply check_wfm_input_event.
Defined.

Definition check_wfm_output_event dbt oe : wfm_output_event dbt oe + wf_error.
destruct oe.

- (* OTraceInput *)
  destruct (@check_wfm_input_event dbt ie); [ | die_auto ].
  left. econstructor; eassumption.

- (* OTraceBegin *)
  destruct (lookup_type dbt rn) eqn:?; [ | die (WfeNoSuchRecord rn) ].
  left. econstructor; eassumption.

- (* OTraceEnd *)
  destruct (lookup_type dbt rn) eqn:?; [ | die (WfeNoSuchRecord rn) ].
  left. econstructor; eassumption.

- (* OHwWrite *)
  destruct (lookup_type dbt rn) eqn:?; [ | die (WfeNoSuchRecord rn) ].
  left. econstructor; eassumption.

- (* OScheduleCallback *)
  destruct (lookup_type dbt rn) as [ rt | ] eqn:?; [ | die (WfeNoSuchRecord rn) ].
  destruct (@check_list _ _ ops (check_wfm_instr dbt rt)); [ | die_auto ].
  left. econstructor; eassumption.

Defined.

Definition check_wfm_output_events dbt oes : Forall (wfm_output_event dbt) oes + wf_error.
eapply check_list.
eapply check_wfm_output_event.
Defined.

Require Import Arith.
Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import Sorted.
Require Import Omega.
Require Import Psatz.


Require Import v1.NeutronTactics.
Require Import v1.Util.
Require Import v1.Multi.
Require Import v1.MForall.
Require Import v1.ListLemmas.
Require Import v1.Wf.
Require Import v1.Terminate.
Require Import v1.Preservation.
Require Import v1.Queue.
Require Import v1.System.
Require Import v1.SystemWf.
Require Import v1.Expr.
Require v1.ExprDbl.
Require v1.ExprDblStr.
Require v1.ExprAbs.
Require v1.ExprAbsProofs.

Require Import v1.EpicsTypes.
Require v1.EpicsRecordsBase.
Require v1.EpicsRecords.
Require Import v1.FloatAux.
Require Import v1.FloatAbs.
Require Import v1.FloatAbsBase.
Require Import v1.Step.
Require Import v1.StepAux.
Require v1.ControlFlow.

Set Default Timeout 10.
Set Implicit Arguments.

Module ERB := EpicsRecordsBase.
Module ER := EpicsRecords.
Module Abs := FloatAbs.
Module CF := ControlFlow.



(* list lemmas *)

Lemma lookup_abs_type : forall dba dbt rn ra rt,
    dbt = database_abs_type dba ->
    rt = record_abs_type ra ->
    lookup_abs dba rn = Some ra ->
    lookup_type dbt rn = Some rt.
first_induction rn; intros0 Heqdbt Heqrt Hnrs;
destruct dba; simpl in *; try congruence.
- subst. simpl. congruence.
- subst. simpl in *. eauto.
Qed.

Lemma lookup_abs_type_eq : forall dba dbt rn ra rt,
    dbt = database_abs_type dba ->
    lookup_abs dba rn = Some ra ->
    lookup_type dbt rn = Some rt ->
    rt = record_abs_type ra.
first_induction rn; intros0 Heqdbt Hls Hlt;
subst dbt; destruct dba; simpl in *; try congruence.
eapply IHrn; eauto.
Qed.




Definition double_abs (d : e_double) : abs_value :=
    match B2Z_safe d with
    | Some x => Some (x, x)
    | None => None
    end.

Definition enum_abs {max} (e : e_enum max) : abs_value :=
    let '(EEnum _ val _) := e in
    Some (val, val).

Definition long_abs (e : e_long) : abs_value :=
    let '(ELong val _) := e in
    Some (val, val).

Definition value_abs (v : value) : abs_value :=
    match v with
    | VDouble d => double_abs d
    | VEnum e => enum_abs e
    | VLong l => long_abs l
    | _ => None
    end.

Definition record_state_abs s :=
    match s with
    | RsCalc (CalcState a2l val) => 
            RaCalc (CalcAbs
                (multi_map double_abs a2l)
                (double_abs val))
    | RsCalcOut (CalcOutState a2l val pval oval tmp0) => 
            RaCalcOut (CalcOutAbs
                (multi_map double_abs a2l)
                (double_abs val)
                (double_abs pval)
                (double_abs oval)
                (double_abs tmp0))
    | RsStrCalcOut (StrCalcOutState a2l _ val _ pval oval _ tmp0) =>
            RaStrCalcOut (StrCalcOutAbs
                (multi_map double_abs a2l)
                (double_abs val)
                (double_abs pval)
                (double_abs oval)
                (double_abs tmp0))
    | RsArrayCalcOut n (ArrayCalcOutState _ a2l _ val _ pval oval _ tmp0) =>
            RaArrayCalcOut _ (ArrayCalcOutAbs n
                (multi_map double_abs a2l)
                (double_abs val)
                (double_abs pval)
                (double_abs oval)
                (double_abs tmp0))
    | RsFanout (FanoutState) =>
            RaFanout (FanoutAbs)
    | RsAnalogIn (AnalogInState val) =>
            RaAnalogIn (AnalogInAbs
                (double_abs val))
    | RsAnalogOut (AnalogOutState val pval) =>
            RaAnalogOut (AnalogOutAbs
                (double_abs val)
                (double_abs pval))
    | RsBinaryIn (BinaryInState val) =>
            RaBinaryIn (BinaryInAbs
                (enum_abs val))
    | RsBinaryOut (BinaryOutState val) =>
            RaBinaryOut (BinaryOutAbs
                (enum_abs val))
    | RsMBBO (MBBOState val) =>
            RaMBBO (MBBOAbs
                (enum_abs val))
    | RsStringIn (StringInState _) =>
            RaStringIn (StringInAbs)
    | RsStringOut (StringOutState _) =>
            RaStringOut (StringOutAbs)
    | RsLongIn (LongInState val) =>
            RaLongIn (LongInAbs
                (long_abs val))
    | RsLongOut (LongOutState val) =>
            RaLongOut (LongOutAbs
                (long_abs val))
    | RsDFanout (DFanoutState val) =>
            RaDFanout (DFanoutAbs
                (double_abs val))
    | RsSeq (SeqState do1_to_a _) =>
            RaSeq (SeqAbs
                (multi_map double_abs do1_to_a))
    | RsWaveform ty n (WaveformState _ _ val) =>
            RaWaveform _ _ (WaveformAbs ty n)
    | RsSubarray ty n m (SubarrayState _ _ _ val tmp0) =>
            RaSubarray _ _ _ (SubarrayAbs ty n m)
    | RsAsyn (AsynState) =>
            RaAsyn (AsynAbs)
    end.

Definition database_state_abs (dbs : database_state) : database_abs :=
    map record_state_abs dbs.



(*
Definition interp_update_record f : forall dba rn,
    forall ra ra',
    lookup_abs dba rn = Some ra ->
    f ra = Some ra' ->
    { dba' | Abs.update_record f dba rn = Some dba' }.
first_induction dba; destruct rn; simpl in *; intros0 Hrs Hf.
- congruence.
- congruence.
- fancy_injr Hrs. rewrite Hf.
  eexists. reflexivity.
- forward eapply IHdba as [ dba' Hdba' ]; eauto.  rewrite Hdba'.
  eexists. reflexivity.
Defined.


Definition interp_write_field ra fn val :
    forall rt vt,
    record_abs_type ra = rt ->
    record_has_field rt fn vt ->
    { ra' | Abs.write_field ra fn val = Some ra' }.
intros0 Hrst Hrhf.
destruct (Abs.write_field _ _ _) eqn:Heq.
{ eexists. reflexivity. }

exfalso.
invc Hrhf;
destruct_record_abs ra; try discriminate.
Defined.

Definition interp_write_record_field dba rn fn val :
    forall dbt vt,
    database_abs_type dba = dbt ->
    wfm_field_access dbt rn fn vt ->
    { dba' | Abs.write_record_field dba rn fn val = Some dba' }.
intros0 Hdbt Hwf.
destruct (Abs.write_record_field _ _ _ _) eqn:Heq.
{ eexists. reflexivity. }

exfalso.

invc Hwf.

forward eapply lookup_length_ex with (ys := dba) as [ ra Hra ]; eauto using map_length.
forward eapply lookup_abs_type_eq; try eassumption; eauto.
forward eapply (@interp_write_field ra fn val) as [ ra' Hra' ]; eauto.
{ subst. eassumption. }

unfold Abs.write_record_field in Heq.
forward eapply interp_update_record as [ dba' Hdba' ];
[ | | rewrite Hdba' in Heq; discriminate Heq ]; eauto.
Defined.
*)

Definition merge abs1 abs2 :=
    match abs1, abs2 with
    | Some (min1, max1), Some (min2, max2) =>
            Some (Z.min min1 min2, Z.max max1 max2)
    | _, _ => None
    end.

Definition merge_field ra fn abs :=
    Abs.read_field ra fn >>= fun abs' =>
    Abs.write_field ra fn (merge abs abs').

Definition merge_record_field dba rn fn abs :=
    Abs.update_record (fun ra => merge_field ra fn abs) dba rn.


Definition havoc_abs a :=
    match a with
    | RaCalc (CalcAbs _ _) => 
            RaCalc (CalcAbs (multi_rep 12 None) None)
    | RaCalcOut (CalcOutAbs _ _ _ _ _) => 
            RaCalcOut (CalcOutAbs (multi_rep 12 None) None None None None)
    | RaStrCalcOut (StrCalcOutAbs _ _ _ _ _) => 
            RaStrCalcOut (StrCalcOutAbs (multi_rep 12 None) None None None None)
    | RaArrayCalcOut n (ArrayCalcOutAbs _ _ _ _ _ _) => 
            RaArrayCalcOut _ (ArrayCalcOutAbs n (multi_rep 12 None) None None None None)
    | RaFanout (FanoutAbs) =>
            RaFanout (FanoutAbs)
    | RaAnalogIn (AnalogInAbs _) =>
            RaAnalogIn (AnalogInAbs None)
    | RaAnalogOut (AnalogOutAbs _ _) =>
            RaAnalogOut (AnalogOutAbs None None)
    | RaBinaryIn (BinaryInAbs _) =>
            RaBinaryIn (BinaryInAbs None)
    | RaBinaryOut (BinaryOutAbs _) =>
            RaBinaryOut (BinaryOutAbs None)
    | RaMBBO (MBBOAbs _) =>
            RaMBBO (MBBOAbs None)
    | RaStringIn (StringInAbs) =>
            RaStringIn (StringInAbs)
    | RaStringOut (StringOutAbs) =>
            RaStringOut (StringOutAbs)
    | RaLongIn (LongInAbs _) =>
            RaLongIn (LongInAbs None)
    | RaLongOut (LongOutAbs _) =>
            RaLongOut (LongOutAbs None)
    | RaDFanout (DFanoutAbs _) =>
            RaDFanout (DFanoutAbs None)
    | RaSeq (SeqAbs _) =>
            RaSeq (SeqAbs (multi_rep 10 None))
    | RaWaveform ty n (WaveformAbs _ _) =>
            RaWaveform _ _ (WaveformAbs ty n)
    | RaSubarray ty n m (SubarrayAbs _ _ _) =>
            RaSubarray _ _ _ (SubarrayAbs ty n m)
    | RaAsyn (AsynAbs) =>
            RaAsyn (AsynAbs)
    end.

Definition clamp_abs low high abs :=
    match abs with
    | Some (low', high') =>
            let low'' := Z.max low low' in
            let high'' := Z.min high high' in
            Some (low'', high'')
    | None => None
    end.

Definition interp_convert abs new_ty :=
    match new_ty with
    | TDouble => abs
    | TLong => clamp_abs (-LONG_MAX) (LONG_MAX - 1) abs
    | TEnum max => clamp_abs 0 (max - 1) abs
    | _ => None
    end.

Definition interp_set_const dba rn fn val :=
    let abs := value_abs val in
    merge_record_field dba rn fn abs.

Definition interp_copy dba rn fn_src (src_ty : field_type) fn_dest dest_ty :=
    let f ra :=
        Abs.read_field ra fn_src >>= fun abs =>
        let abs' := interp_convert abs dest_ty in
        merge_field ra fn_dest abs' in
    Abs.update_record f dba rn.

Definition interp_read_link dba rn il (il_ty : field_type) fn f_ty :=
    Abs.read_record_field dba (fl_rn il) (fl_fn il) >>= fun abs =>
    let abs' := interp_convert abs f_ty in
    merge_record_field dba rn fn abs'.

Definition interp_write_link dba rn fn (f_ty : field_type) ol ol_ty :=
    Abs.read_record_field dba rn fn >>= fun abs =>
    let abs' := interp_convert abs ol_ty in
    merge_record_field dba (fl_rn ol) (fl_fn ol) abs'.

Definition interp_calculate dba rn e fn_out :=
    lookup dba rn >>= fun ra =>
    ExprAbs.denote e >>= fun f =>
    match ra with
    | RaCalc (CalcAbs a2l val) =>
            let (a2l', result) := f a2l in
            let a2l'' := multi_zip merge a2l a2l' in
            Some (RaCalc (CalcAbs a2l'' val), result)
    | RaCalcOut (CalcOutAbs a2l val pval oval tmp0) =>
            let (a2l', result) := f a2l in
            let a2l'' := multi_zip merge a2l a2l' in
            Some (RaCalcOut (CalcOutAbs a2l'' val pval oval tmp0), result)
    | _ => None
    end >>= fun x => let '(ra', result) := x in
    merge_field ra' fn_out result >>= fun ra'' =>
    Abs.update_record (fun _ => Some ra'') dba rn.

Definition interp_havoc_update dba rn :=
    Abs.update_record (fun ra => Some (havoc_abs ra)) dba rn.

Definition interp_havoc_write dba (rn : record_name) ol (ol_ty : field_type) :=
    merge_record_field dba (fl_rn ol) (fl_fn ol) None.

Definition interp_op dba rn op :=
    match op with
    | MSetConst fn val =>
            interp_set_const dba rn fn val
    | MCopy fn_src src_ty fn_dest dest_ty =>
            interp_copy dba rn fn_src src_ty fn_dest dest_ty
    | MReadLink il il_ty fn f_ty =>
            interp_read_link dba rn il il_ty fn f_ty
    | MWriteLink fn f_ty ol ol_ty =>
            interp_write_link dba rn fn f_ty ol ol_ty
    | MCalculate expr fn_out =>
            interp_calculate dba rn expr fn_out
    | MHavocUpdate =>
            interp_havoc_update dba rn
    | MHavocWrite ol ol_ty =>
            interp_havoc_write dba rn ol ol_ty
    | _ => Some dba
    end.

Definition interp_op_rec rn :=
    let fix go dba op :=
        let fix go_list dba ops :=
            match ops with
            | [] => Some dba
            | op :: ops => go dba op >>= fun dba => go_list dba ops
            end in
        interp_op dba rn op >>= fun dba =>
        match op with
        | MCalcCond _ _ _ body => go_list dba body
        | MScheduleCallback _ code => go_list dba code
        | _ => Some dba
        end in go.

Definition interp_op_rec_list rn :=
    let go := interp_op_rec rn in
    let fix go_list dba ops :=
        match ops with
        | [] => Some dba
        | op :: ops => go dba op >>= fun dba => go_list dba ops
        end in go_list.

Definition interp_ops dba rn ops := interp_op_rec_list rn dba ops.

Definition interp_prog dba dbp :=
    let fix go dba xs :=
        match xs with
        | [] => Some dba
        | (rn, rp) :: xs =>
            interp_ops dba rn (rp_code rp) >>= fun dba =>
            go dba xs
        end in
    go dba (numbered dbp).



Inductive refine_val : abs_value -> value -> Prop :=
| RvTop : forall v, refine_val None v
| RvDouble : forall d z min max,
        fwhole_eq d z ->
        (min <= z <= max)%Z ->
        refine_val (Some (min, max)) (VDouble d).

Inductive refine_record : record_abs -> record_state -> Prop :=
| RefineRecord : forall ra rs,
        record_abs_type ra = record_state_type rs ->
        (forall fn,
            forall va, Abs.read_field ra fn = Some va ->
            forall vs, read_field rs fn = Some vs ->
            refine_val va vs) ->
        refine_record ra rs.

Definition refine dba dbs :=
    Forall2 refine_record dba dbs.



Inductive wider : abs_value -> abs_value -> Prop :=
| WiderTop : forall a, wider a None
| WiderRange : forall min1 max1 min2 max2,
        min2 <= min1 ->
        max1 <= max2 ->
        wider (Some (min1, max1)) (Some (min2, max2)).

Lemma wider_refl : forall a, wider a a.
destruct a; try constructor.
destruct p; try constructor; lia.
Qed.

Lemma refine_val_wider : forall a a' v,
    refine_val a v ->
    wider a a' ->
    refine_val a' v.
destruct a, a', v; intros0 Hr Hw;
invc Hr; invc Hw; try solve [ econstructor ].
- econstructor.
  + eassumption.
  + lia.
Qed.


Lemma lookup_refine : forall dbs rn rs dba ra,
    refine dba dbs ->
    lookup dbs rn = Some rs ->
    lookup dba rn = Some ra ->
    refine_record ra rs.
unfold lookup, refine. intros.
eapply Forall2_nth_error; eauto.
Qed.

Lemma read_record_field_refine : forall dbs rn fn val dba ra a,
    refine dba dbs ->
    read_record_field dbs rn fn = Some val ->
    lookup dba rn = Some ra ->
    Abs.read_field ra fn = Some a ->
    refine_val a val.
intros0 Hr Hst_rrf Habs_rn Habs_fn.

unfold read_record_field in Hst_rrf.
destruct (lookup_state _ _) eqn:Hst_rn; [ | discriminate ].
simpl in Hst_rrf. rename Hst_rrf into Hst_fn.
forward eapply lookup_refine as HH; eauto.
invc HH. eauto.
Qed.


Lemma update_record_lookup_eq : forall f dbs rn dbs' rn' rs rs',
    update_record f dbs rn = Some dbs' ->
    lookup dbs rn' = Some rs ->
    lookup dbs' rn' = Some rs' ->
    rn = rn' ->
    f rs = Some rs'.
first_induction rn; intros0 Hup Hlook Hlook' Hrn; subst rn'.

- destruct dbs, dbs'; simpl in *; try discriminate.
  break_match; try discriminate.
  congruence.

- destruct dbs, dbs'; simpl in *; try discriminate.
  break_match; try discriminate.
  inject_some.
  specialize (IHrn ?? ?? ?? ?? ?? ?? ** ** ** ***). assumption.
Qed.

Lemma update_record_lookup_ne : forall f dbs rn dbs' rn' rs rs',
    update_record f dbs rn = Some dbs' ->
    lookup dbs rn' = Some rs ->
    lookup dbs' rn' = Some rs' ->
    rn <> rn' ->
    rs = rs'.
first_induction rn'; intros0 Hup Hlook Hlook' Hrn.

- destruct rn; try congruence.
  destruct dbs, dbs'; simpl in *; try discriminate.
  break_match; try discriminate.
  congruence.

- destruct dbs, dbs'; simpl in *; try discriminate.
  destruct rn.
  + break_match; try discriminate.
    congruence.
  + break_match; try discriminate.
    inject_some. eapply IHrn'; eauto.
Qed.

Lemma update_record_length : forall f dbs rn dbs',
    update_record f dbs rn = Some dbs' ->
    length dbs = length dbs'.
induction dbs; intros0 Hup; simpl in *; try discriminate.
break_match; break_match; try discriminate.

- destruct dbs'; inject_some. simpl. reflexivity.

- destruct dbs'; inject_some. simpl.
  specialize (IHdbs ?? ?? **). congruence.
Qed.

Lemma update_record_forall : forall f dbs rn dbs' rs0,
    update_record f dbs rn = Some dbs' ->
    lookup dbs rn = Some rs0 ->
    Forall2 (fun rs rs' => rs = rs' \/ (rs = rs0 /\ f rs = Some rs')) dbs dbs'.
intros0 Hup Hlook.
eapply nth_error_Forall2.
  { eauto using update_record_length. }
intros rn' rs rs' ? ?.
destruct (eq_nat_dec rn rn').
- right. split.
  + subst. unfold lookup in Hlook. congruence.
  + eapply update_record_lookup_eq; eauto.
- left.
  eapply update_record_lookup_ne; eauto.
Qed.


Lemma update_record_refine : forall dba f dbs rn dbs',
    (forall ra rs rs',
        lookup dba rn = Some ra ->
        lookup dbs rn = Some rs ->
        f rs = Some rs' ->
        refine_record ra rs ->
        refine_record ra rs') ->
    update_record f dbs rn = Some dbs' ->
    refine dba dbs ->
    refine dba dbs'.
first_induction dbs; destruct rn; intros0 Hf Hupd Href; try discriminate; simpl in *.
- rename a into rs. invc Href. rename x into ra. rename l into dba.
  destruct (f rs) as [ rs' | ] eqn:?; [ | discriminate Hupd ].
  inject_some.
  specialize (Hf ?? ?? ?? *** *** ** **).
  constructor; eauto.
- rename a into rs. invc Href. rename x into ra. rename l into dba.
  destruct (update_record _ _ _) as [ dbs'' | ] eqn:?; [ | discriminate Hupd ].
  inject_some.
  constructor; eauto.
  eapply IHdbs; eauto.
Qed.


Require Import ProofIrrelevance.

Lemma write_field_read_eq' : forall rs fn val rs',
    write_field rs fn val = Some rs' ->
    read_field rs' fn = Some val.
intros0 Hwf; destruct_record rs as [st]; destruct fn;
try match goal with [ |- read_field _ (f_tmp ?n) = _ ] => destruct n end;
try discriminate Hwf.

all: destruct val; try discriminate Hwf.

all: cbv  [write_field bind_option unwrap_double unwrap_string unwrap_long] in Hwf;
     try break_match; try discriminate; (* VEnum cases: get a separate eqn for unwrap_enum *)
     fancy_injr <- Hwf; destruct st;
     cbv -[multi_get multi_set];
     try rewrite multi_set_get; (* multi fields *)
     try reflexivity.

all: try solve [
    (* VEnum handling *)
    simpl in Heqo; break_match; try discriminate;
    subst max;
    unfold eq_rect_r in *; rewrite <- eq_rect_eq in *;
    congruence
].

all: try solve [
    (* VArray handling *)
    simpl in *;
    do 2 (break_match; try discriminate);
    subst elem; subst size;
    unfold eq_rect_r in *; rewrite <- eq_rect_eq, <- eq_rect_eq in *;
    congruence
].

Qed.

Lemma write_field_read_eq : forall rs fn val rs' fn',
    write_field rs fn val = Some rs' ->
    fn = fn' ->
    read_field rs' fn' = Some val.
intros0 Hwf Hfn.  subst fn'.  eauto using write_field_read_eq'.
Qed.

Lemma write_field_read_ne : forall rs fn val rs' fn',
    write_field rs fn val = Some rs' ->
    fn <> fn' ->
    read_field rs fn' = read_field rs' fn'.
intros0 Hwf Hne; destruct_record rs as [st]; destruct fn;
try match type of Hne with f_tmp ?n <> _ => destruct n end;
try discriminate Hwf.

all: cbv  [write_field bind_option unwrap_double unwrap_string unwrap_long] in Hwf;
     repeat break_match; try discriminate; (* both VEnum and other cases *)
     fancy_injr <- Hwf; destruct st;
     cbv -[multi_get multi_set];
     destruct fn'; try reflexivity; try congruence.

all: try solve [
    (* multi field case *)
    destruct i as [i Hi], i0 as [i0 Hi0];
    destruct (eq_nat_dec i i0);
        [ contradict Hne; subst; f_equal; f_equal; eapply proof_irrelevance | ];
    rewrite multi_set_get_other by (simpl; congruence);
    reflexivity
].

(* f_tmp cases *)
all: match type of Hne with _ <> f_tmp ?n => destruct n end; try congruence.
Qed.

Lemma write_field_refine : forall rs fn val rs' ra a,
    refine_record ra rs ->
    write_field rs fn val = Some rs' ->
    Abs.read_field ra fn = Some a ->
    refine_val a val ->
    refine_record ra rs'.
intros0 Hr Hst_fn Habs_fn Hrv.
invc Hr. constructor.  { erewrite <- write_field_preserves_state_type; eauto. }
intros fn' ? Habs_fn' ? Hst_fn'.
destruct (field_name_eq_dec fn fn').

- forward eapply write_field_read_eq with (fn := fn) (fn' := fn'); eauto.
  congruence.

- forward eapply write_field_read_ne with (fn := fn) (fn' := fn'); eauto.
  on _, eapply_; eauto. congruence.

Qed.

Lemma write_record_field_refine : forall dbs rn fn val dbs' dba ra a,
    refine dba dbs ->
    write_record_field dbs rn fn val = Some dbs' ->
    lookup dba rn = Some ra ->
    Abs.read_field ra fn = Some a ->
    refine_val a val ->
    refine dba dbs'.
intros0 Hr Hst_wrf Habs_rn Habs_fn Hrv.

unfold write_record_field in Hst_wrf.
unfold refine in *.

forward eapply lookup_length_ex with (ys := dbs) as HH; eauto using Forall2_length.
  destruct HH as [rs Hst_rn].
eapply nth_error_Forall2.
  { erewrite Forall2_length by eassumption. eauto using update_record_length. }
intros rn' ra' rs' Hra Hrs.
destruct (eq_nat_dec rn rn').

- subst rn'.
  replace ra' with ra in * by (unfold lookup in *; congruence).
  forward eapply update_record_lookup_eq; eauto. cbv beta in *.
  eapply write_field_refine; eauto.
  eapply Forall2_nth_error; eauto.

- forward eapply lookup_length_ex with (ys := dbs) as HH; eauto.
    symmetry. eauto using update_record_length.
    destruct HH as [rs0' Hrs0'].
  forward eapply update_record_lookup_ne with (rn := rn) (rn' := rn'); eauto.
  eapply Forall2_nth_error; eauto. unfold lookup in *. congruence.
Qed.


Lemma convert_value_noop : forall val ty,
    value_type val = ty ->
    convert_value val ty = Some val.
intros0 Hty.
destruct val, ty; try discriminate Hty; try reflexivity.

(* enum *)
- simpl in Hty. invc Hty. simpl. repeat break_match.
  + do 3 f_equal. eapply proof_irrelevance.
  + exfalso. lia.

(* long *)
- simpl. break_match. reflexivity.

(* array *)
- simpl in Hty. invc Hty. simpl. repeat break_match.
  + reflexivity.
  + congruence.
  + congruence.
Qed.







Inductive error :=
| ENoRecord : record_name -> error
| ENoField : field_name -> error
| ENotCalc : record_name -> error
| EBadExpr : record_name -> error
| ENotWider : abs_value -> abs_value -> error
| EBadConst : value -> abs_value -> error
| EBadType : field_type -> field_type -> error
| ENotImplemented : micro -> error
| ELenMismatch : nat -> nat -> error
.

Ltac die x := right; exact x.
Ltac die_auto :=
    match goal with
    | [ e : list error |- _ ] => die e
    end.

Definition check_wider : forall a a',
    { wider a a' } + { ~ wider a a' }.
destruct a, a'; try solve [ right; inversion 1 | left; econstructor ].
- destruct p as [min1 max1], p0 as [min2 max2].
  destruct (Z_le_dec min2 min1); [ | right; inversion 1; lia ].
  destruct (Z_le_dec max1 max2); [ | right; inversion 1; lia ].
  left. constructor; assumption.
Qed.

Definition check_refine_const : forall a v,
    { refine_val a v } + { ~ refine_val a v }.
destruct a, v; try solve [left; constructor | right; inversion 1].

- rename e into x.
  destruct (B2Z_safe x) as [ z | ] eqn:?; cycle 1.
    { right. inversion 1. forward eapply B2Z_safe_complete; eauto. congruence.  }

  destruct p as [min max].
  destruct (Z_le_gt_dec min z); cycle 1.
    { right. inversion 1. forward eapply B2Z_safe_complete; eauto.
      replace z0 with z in * by congruence. lia. }
  destruct (Z_le_gt_dec z max); cycle 1.
    { right. inversion 1. forward eapply B2Z_safe_complete; eauto.
      replace z0 with z in * by congruence. lia. }

  left. econstructor; eauto using B2Z_safe_correct.
Qed.


Definition db_step_ok dba rn op :=
    forall dbs dbs',
    database_state_type dbs = database_abs_type dba ->
    refine dba dbs ->
    db_step rn op dbs dbs' ->
    refine dba dbs'.

Definition check_set_const : forall dba rn fn val,
    db_step_ok dba rn (MSetConst fn val) + list error.
intros.
destruct (lookup dba rn) as [ra | ] eqn:?; [ | die [ENoRecord rn] ].
destruct (Abs.read_field ra fn) as [dest_abs | ] eqn:?; [ | die [ENoField fn] ].
destruct (check_refine_const dest_abs val); [ | die [EBadConst val dest_abs] ].

left. unfold db_step_ok. intros0 Hty Hr Hstep. invc Hstep.
eapply write_record_field_refine; try eassumption.
Defined.

Definition check_copy : forall dba rn fn_src src_ty fn_dest dest_ty,
    db_step_ok dba rn (MCopy fn_src src_ty fn_dest dest_ty) + list error.
intros.
destruct (lookup dba rn) as [ra | ] eqn:?; [ | die [ENoRecord rn] ].
destruct (Abs.read_field ra fn_src) as [src_abs | ] eqn:?; [ | die [ENoField fn_src] ].
destruct (Abs.read_field ra fn_dest) as [dest_abs | ] eqn:?; [ | die [ENoField fn_dest] ].
destruct (check_wider src_abs dest_abs); [ | die [ENotWider src_abs dest_abs] ].
destruct (field_type_eq_dec src_ty dest_ty); [ | die [EBadType src_ty dest_ty] ].

left. unfold db_step_ok. intros0 Hty Hr Hstep. invc Hstep.
eapply write_record_field_refine; try eassumption.
eapply refine_val_wider; try eassumption.
rewrite convert_value_noop in *; eauto. inject_some.
eapply read_record_field_refine; try eassumption.
Defined.

Definition check_read_link : forall dba rn il il_ty fn f_ty,
    db_step_ok dba rn (MReadLink il il_ty fn f_ty) + list error.
intros.
destruct (lookup dba rn) as [ra | ] eqn:?; [ | die [ENoRecord rn] ].
destruct (lookup dba (fl_rn il)) as [ra' | ] eqn:?; [ | die [ENoRecord (fl_rn il)] ].
destruct (Abs.read_field ra' (fl_fn il)) as [src_abs | ] eqn:?; [ | die [ENoField (fl_fn il)] ].
destruct (Abs.read_field ra fn) as [dest_abs | ] eqn:?; [ | die [ENoField fn] ].
destruct (check_wider src_abs dest_abs); [ | die [ENotWider src_abs dest_abs] ].
destruct (field_type_eq_dec il_ty f_ty); [ | die [EBadType il_ty f_ty] ].

left. unfold db_step_ok. intros0 Hty Hr Hstep. invc Hstep.
eapply write_record_field_refine; try eassumption.
eapply refine_val_wider; try eassumption.
rewrite convert_value_noop in *; eauto. inject_some.
eapply read_record_field_refine; try eassumption.
Defined.

Definition check_write_link : forall dba rn fn f_ty ol ol_ty,
    db_step_ok dba rn (MWriteLink fn f_ty ol ol_ty) + list error.
intros.
destruct (lookup dba rn) as [ra | ] eqn:?; [ | die [ENoRecord rn] ].
destruct (lookup dba (fl_rn ol)) as [ra' | ] eqn:?; [ | die [ENoRecord (fl_rn ol)] ].
destruct (Abs.read_field ra fn) as [src_abs | ] eqn:?; [ | die [ENoField fn] ].
destruct (Abs.read_field ra' (fl_fn ol)) as [dest_abs | ] eqn:?; [ | die [ENoField (fl_fn ol)] ].
destruct (check_wider src_abs dest_abs); [ | die [ENotWider src_abs dest_abs] ].
destruct (field_type_eq_dec f_ty ol_ty); [ | die [EBadType f_ty ol_ty] ].

left. unfold db_step_ok. intros0 Hty Hr Hstep. invc Hstep.
eapply write_record_field_refine; try eassumption.
eapply refine_val_wider; try eassumption.
rewrite convert_value_noop in *; eauto. inject_some.
eapply read_record_field_refine; try eassumption.
Defined.

Definition check_calc : forall ra,
    { a2l, val | ra = RaCalc (CalcAbs a2l val) } +
    { forall abs, ra <> RaCalc abs }.
intros.
destruct_record_abs ra; try solve [right; intros; discriminate ].
- left. destruct a. eexists. reflexivity.
Qed.

Definition check_list : forall A (P : A -> Prop) xs
        (check_one : forall x, P x + list error),
    Forall P xs + list error.
induction xs; intros.
- left. constructor.
- rename a into x.
  destruct (check_one x); [ | die_auto ].
  destruct (IHxs check_one); [ | die_auto ].
  left. constructor; eauto.
Defined.

Definition check_multi : forall n (A : Set) (P : A -> Prop) (x : multi n A)
        (check_one : forall x, P x + list error),
    MForall P x + list error.
intros.
destruct (check_list P (multi_to_list x) check_one); [ | die_auto ].
left. rewrite MForall_Forall. auto.
Defined.

Definition check_list2 : forall A B (P : A -> B -> Prop) xs ys
        (check_one : forall x y, P x y + list error),
    Forall2 P xs ys + list error.
induction xs; destruct ys; intros.
- left. constructor.
- die [ELenMismatch 0 (S (length ys))].
- die [ELenMismatch (S (length xs)) 0].
- rename a into x. rename b into y.
  destruct (check_one x y); [ | die_auto ].
  destruct (IHxs ys check_one); [ | die_auto ].
  left. constructor; eauto.
Defined.

Definition check_multi2 : forall n (A B : Set) (P : A -> B -> Prop)
        (x : multi n A) (y : multi n B)
        (check_one : forall x y, P x y + list error),
    MForall2 P x y + list error.
intros.
destruct (check_list2 P (multi_to_list x) (multi_to_list y) check_one); [ | die_auto ].
left. rewrite MForall2_Forall2. auto.
Defined.

Definition check_wider' : forall val val',
    wider val val' + list error.
intros.
destruct (check_wider val val'); [ | die [ENotWider val val'] ].
left. auto.
Qed.

Definition state_A_to_L s :=
    match s with
    | RsCalc st => Some (EpicsRecordsBase.calc_A_to_L st)
    | RsCalcOut st => Some (EpicsRecordsBase.calc_out_A_to_L st)
    | _ => None
    end.

Definition abs_A_to_L a :=
    match a with
    | RaCalc abs => Some (FloatAbsBase.calc_A_to_L abs)
    | RaCalcOut abs => Some (FloatAbsBase.calc_out_A_to_L abs)
    | _ => None
    end.

Lemma abs_A_to_L_ex : forall rs ra sa2l,
    refine_record ra rs ->
    state_A_to_L rs = Some sa2l ->
    exists aa2l, abs_A_to_L ra = Some aa2l.
intros0 Hrefine Hsa2l.
destruct_record rs as [st]; try discriminate Hsa2l; destruct st.
all: simpl in Hsa2l; inject_some.
all: invc Hrefine; unfold record_state_type in *.
all: destruct_record_abs ra as [abs]; try discriminate; destruct abs.
all: eexists; reflexivity.
Qed.

Lemma run_calculate_record_effect : forall f fn_out rs rs',
    run_calculate_record f fn_out rs = Some rs' ->
    exists a2l a2l' out',
        state_A_to_L rs = Some a2l /\
        f a2l = (a2l', out') /\
        state_A_to_L rs' = Some a2l' /\
        read_field rs' fn_out = Some (VDouble out').
intros0 Hrun.

destruct_record rs as [ st ]; try discriminate.
all: destruct st; simpl in Hrun.
all: destruct (f _) as (a2l', out') eqn:?.
all: destruct fn_out; try discriminate.
all: inject_some; simpl.
all: eauto 7.
Qed.

Lemma run_calculate_record_preserved : forall f fn_out rs rs' fn,
    run_calculate_record f fn_out rs = Some rs' ->
    (forall i, fn <> f_A_to_L i) ->
    fn <> fn_out ->
    read_field rs' fn = read_field rs fn.
intros0 Hrun Ha2l Hval.
destruct_record rs as [ st ]; try discriminate.
all: destruct st; simpl in Hrun.
all: destruct (f _) as (a2l', out').
all: destruct fn_out; try discriminate.
all: inject_some; simpl.
all: destruct fn; try solve [exfalso; congruence | reflexivity].
Qed.

Lemma A_to_L_state_read_field : forall rs a2l i val,
    state_A_to_L rs = Some a2l ->
    read_field rs (f_A_to_L i) = Some (VDouble val) <-> (a2l !! i) = val.
intros0 Ha2l.
destruct_record rs as [st]; try discriminate; destruct st.
all: simpl in Ha2l; inject_some.
all: compute -[multi_get].
all: intuition congruence.
Qed.

Lemma A_to_L_abs_read_field : forall ra a2l i val,
    abs_A_to_L ra = Some a2l ->
    Abs.read_field ra (f_A_to_L i) = Some val <-> (a2l !! i) = val.
intros0 Ha2l.
destruct_record_abs ra as [abs]; try discriminate; destruct abs.
all: simpl in Ha2l; inject_some.
all: compute -[multi_get].
all: intuition congruence.
Qed.

Lemma A_to_L_MForall2 : forall (P : _ -> _ -> Prop) rs ra sa2l aa2l,
    state_A_to_L rs = Some sa2l ->
    abs_A_to_L ra = Some aa2l ->
    (forall i sv av,
        read_field rs (f_A_to_L i) = Some (VDouble sv) ->
        Abs.read_field ra (f_A_to_L i) = Some av ->
        P sv av) <->
    MForall2 P sa2l aa2l.
intros0 Hrs Hra. split; intro HH.

- rewrite MForall2_forall. intros. subst. eapply HH.
  + rewrite A_to_L_state_read_field; eauto.
  + rewrite A_to_L_abs_read_field; eauto.

- rewrite MForall2_forall in HH. intros. eapply HH.
  + rewrite <- A_to_L_state_read_field; eauto.
  + rewrite <- A_to_L_abs_read_field; eauto.
Qed.

Lemma refine_val_double_iff' : forall dty aty dbl abs,
    (match dty as dty_, aty as aty_
        return ty_denote ExprAbsProofs.D dty_ -> ty_denote ExprAbsProofs.A aty_ -> Prop with
    | ExprDbl.Nil, ExprAbs.Nil => fun dbl abs => True
    | ExprDbl.Dbl, ExprAbs.Abs => fun dbl abs => refine_val abs (VDouble dbl)
    | _, _ => fun dbl abs => False
    end) dbl abs <->
    ExprAbsProofs.refine_value dty aty dbl abs.
intros. split; intro HH.
- destruct dty, aty; try solve [exfalso; auto].
  + destruct dbl, abs. constructor.
  + invc HH; do 2 econstructor; eauto.
- destruct HH; auto.
  on >ExprAbsProofs.refine_dbl, invc.
  all: econstructor; eauto.
Qed.

Lemma refine_val_double_iff : forall dbl abs,
    refine_val abs (VDouble dbl) <->
    ExprAbsProofs.refine_value ExprDbl.Dbl ExprAbs.Abs dbl abs.
intros.
rewrite <- refine_val_double_iff'. split; auto.
Qed.
Hint Rewrite -> refine_val_double_iff.
Hint Rewrite <- refine_val_double_iff.

Lemma refine_record_A_to_L : forall ra rs aa2l sa2l,
    refine_record ra rs ->
    abs_A_to_L ra = Some aa2l ->
    state_A_to_L rs = Some sa2l ->
    MForall2 (fun s a => refine_val a (VDouble s)) sa2l aa2l.
intros. erewrite <- A_to_L_MForall2; eauto.
intros. on >refine_record, invc.  eauto.
Qed.

Lemma refine_record_A_to_L' : forall ra rs aa2l sa2l,
    refine_record ra rs ->
    abs_A_to_L ra = Some aa2l ->
    state_A_to_L rs = Some sa2l ->
    MForall2 (ExprAbsProofs.refine_value ExprDbl.Dbl ExprAbs.Abs) sa2l aa2l.
intros. forward eapply refine_record_A_to_L; eauto.
rewrite -> MForall2_Forall2 in *.
compute -[multi_to_list e_double abs_value]. (* modifies implicit arguments *)
remember (multi_to_list sa2l) as sa2l'.
remember (multi_to_list aa2l) as aa2l'.
list_magic_on (sa2l', (aa2l', tt)).
rewrite <- refine_val_double_iff. auto.
Qed.

Definition is_A_to_L_dec : forall fn,
    { i | fn = f_A_to_L i } + { ~ exists i, fn = f_A_to_L i }.
destruct fn; try solve [ right; inversion 1; discriminate ].
left; eauto.
Defined.

Lemma run_calculate_record_refine : forall expr f f' fn_out rs rs' ra a2l a2l' out out',
    ExprDbl.denote expr = Some f ->
    ExprAbs.denote expr = Some f' ->
    f' a2l = (a2l', out') ->
    abs_A_to_L ra = Some a2l ->
    MForall2 wider a2l' a2l ->
    Abs.read_field ra fn_out = Some out ->
    wider out' out ->
    refine_record ra rs ->
    run_calculate_record f fn_out rs = Some rs' ->
    refine_record ra rs'.
intros0 Hf Hf' Hcalc' Hra_a2l Ha2l Hra_out Hout Hrefine Hcalc_rec.
inv Hrefine. rename H0 into Hrefine'. constructor.
  { erewrite <- run_calculate_record_preserves_state_type; eauto. }
intros0 Hread. intros0 Hread'.
specialize (Hrefine' _ _ Hread).

forward eapply run_calculate_record_effect as HH; eauto.
  destruct HH as (sa2l & sa2l' & sout' & ? & ? & ? & ?).

forward eapply ExprAbsProofs.denote_refine as HH; eauto.
  destruct HH as (f'' & ? & ?).
  replace f'' with f' in * by congruence.
forward refine (ExprAbsProofs.refine_state_fn_noxvar_dbl_abs_inv _ _ _) as Hfrel; eauto.
do 6 spec_evar Hfrel. spec_assert Hfrel; [ | do 2 spec Hfrel by eassumption ].
  { eapply refine_record_A_to_L'; eauto. }
destruct Hfrel as [Hrel_a2l Hrel_out].

destruct (field_name_eq_dec fn fn_out).
  { subst fn.
    replace va with out in * by congruence.
    eapply refine_val_wider; eauto.
    replace vs with (VDouble sout') in * by congruence.
    rewrite refine_val_double_iff. auto. }

destruct (is_A_to_L_dec fn) as [ [i ?] | ? ].
  { subst fn.
    remember (sa2l' !! i) as vdbl. symmetry in Heqvdbl.
    rewrite <- A_to_L_state_read_field in Heqvdbl by eauto.
    rewrite A_to_L_abs_read_field in Hread by eauto.
    replace vs with (VDouble vdbl) by congruence.
    rewrite A_to_L_state_read_field in Heqvdbl by eauto.
    subst va. subst vdbl.
    eapply refine_val_wider; cycle 1.  { eapply MForall2_get; try eassumption. }
    rewrite refine_val_double_iff. eapply MForall2_get. auto. }

  { eapply Hrefine'.
    erewrite <- run_calculate_record_preserved; try eassumption.
    intros. intro. on _, eapply_. eauto. }

Qed.


Definition check_calculate : forall dba rn expr fn_out,
    db_step_ok dba rn (MCalculate expr fn_out) + list error.
intros.
destruct (lookup dba rn) as [ra | ] eqn:?; [ | die [ENoRecord rn] ].
destruct (abs_A_to_L ra) as [a2l_abs | ] eqn:?; [ | die [ENotCalc rn] ].
destruct (Abs.read_field ra fn_out) as [out_abs | ] eqn:?; [ | die [ENoField fn_out] ].
destruct (ExprAbs.denote expr) as [ calc | ] eqn:?; [ | die [EBadExpr rn] ].
destruct (calc a2l_abs) as [a2l' out'] eqn:?.
destruct (check_multi2 _ _ a2l' a2l_abs check_wider'); [ | die_auto ].
destruct (check_wider out' out_abs); [ | die [ENotWider out' out_abs] ].

left. unfold db_step_ok. intros0 Hty Hr Hstep. invc Hstep.
unfold run_calculate in *.
eapply update_record_refine; try eassumption. intros.
replace ra0 with ra in * by congruence.
eapply run_calculate_record_refine; try eassumption.
Defined.

Definition check_havoc_write : forall dba rn ol ol_ty,
    db_step_ok dba rn (MHavocWrite ol ol_ty) + list error.
intros.
destruct (lookup dba (fl_rn ol)) as [ra | ] eqn:?; [ | die [ENoRecord (fl_rn ol)] ].
destruct (Abs.read_field ra (fl_fn ol)) as [dest_abs | ] eqn:?; [ | die [ENoField (fl_fn ol)] ].
destruct (check_wider None dest_abs); [ | die [ENotWider None dest_abs] ].

left. unfold db_step_ok. intros0 Hty Hr Hstep. invc Hstep.
eapply write_record_field_refine; try eassumption.
eapply refine_val_wider; try eassumption.
constructor.
Defined.

Ltac break_tmp_idx :=
    match goal with
    | [ |- context [ f_tmp ?n ] ] => destruct n
    end.

Lemma read_field_has_field : forall ra fn abs,
    Abs.read_field ra fn = Some abs ->
    exists ty, record_has_field (record_abs_type ra) fn ty.
destruct fn, ra; try break_tmp_idx; intros0 Hrf; try discriminate Hrf.
all: eexists; try constructor.
Qed.

Definition check_havoc_update : forall dba rn,
    db_step_ok dba rn (MHavocUpdate) + list error.
intros.
destruct (lookup dba rn) as [ra | ] eqn:?; [ | die [ENoRecord rn] ].
forward eapply check_list with (xs := all_fields)
    (P := fun fn => Abs.read_field ra fn = None \/ Abs.read_field ra fn = Some None)
    as HH.
  { intro fn.
    destruct (Abs.read_field ra fn) as [abs | ] eqn:?; [ | left; solve [auto] ].
    destruct abs eqn:?; [ die [ENotWider None abs] | ].
    left. auto. }
  destruct HH; [ | die_auto ].

left. unfold db_step_ok. intros0 Hty Hr Hstep. invc Hstep.
eapply update_record_refine; eauto.
intros.
replace ra0 with ra in * by congruence.  clear ra0.
replace rs0 with rs in * by congruence.  clear rs0.
replace rs'0 with rs' in * by congruence.  clear rs'0.

on >refine_record, invc.
constructor. { congruence. }
intros.

assert (In fn all_fields).
  { forward eapply read_field_has_field; eauto. break_exists.
    eauto using in_all_fields. }
on >Forall, fun H => rename H into Hfa. rewrite Forall_forall in Hfa.
specialize (Hfa ?? **). destruct Hfa.
  { find_rewrite. discriminate. }
find_rewrite.
(* A lot of tactics are extremely slow at this poirt for some reason.
   Even `on (Some _ = Some va), fun H => clear -H` times out... *)
generalize dependent va. clear. intros.
inject_some. constructor.
Qed.

Definition check_db_step : forall dba rn op,
    db_step_ok dba rn op + list error.
intros.
destruct op eqn:?;
try solve [left; inversion 3]. (* trivial result for unsupported ops *)

- eapply check_set_const.
- eapply check_copy.
- eapply check_read_link.
- eapply check_write_link.
- eapply check_calculate.
- die [ENotImplemented op]. (* CalculateStr *)
- eapply check_havoc_update.
- eapply check_havoc_write.
Defined.


Definition step_ok dba rn op :=
    forall dbp dbs dbs' stk code stk' oes,
    let state := State dbs (Frame rn (op :: code) :: stk) in
    let state' := State dbs' stk' in
    database_state_type dbs = database_abs_type dba ->
    refine dba dbs ->
    step dbp state state' oes ->
    refine dba dbs'.

Lemma db_op_output_op_disjoint : forall op,
    is_db_op op = true ->
    is_output_op op = true ->
    False.
destruct op; simpl; intros; congruence.
Qed.

Definition check_step' : forall dba rn op,
    step_ok dba rn op + list error.
intros.
destruct (is_db_op op) eqn:?;
destruct (is_output_op op) eqn:?;
try solve [exfalso; eapply db_op_output_op_disjoint; eassumption].
3: destruct op eqn:?; try solve [exfalso; discriminate].

- (* db_step *)
  destruct (check_db_step dba rn op) as [Hok | ?]; [ | die_auto ].

  left. unfold step_ok. intros0 Hty Hr Hstep.
  invc Hstep; try discriminate; cycle 1.
    { destruct op; try discriminate; on >output_step, invc. }
  eapply Hok; eauto.

- (* output_step *)
  left. unfold step_ok. intros0 Hty Hr Hstep.
  invc Hstep; try discriminate.
    { destruct op; try discriminate; on >db_step, invc. }
  assumption.

- (* Process *)
  left. unfold step_ok. intros0 Hty Hr Hstep.
  invc Hstep; [on >db_step, invc | on >output_step, invc | ].
  assumption.

- (* CalcCond *)
  left. unfold step_ok. intros0 Hty Hr Hstep.
  invc Hstep; [on >db_step, invc | on >output_step, invc | | ].
  all: assumption.

- (* CheckPACT *)
  left. unfold step_ok. intros0 Hty Hr Hstep.
  invc Hstep; [on >db_step, invc | on >output_step, invc | | ].
  all: assumption.

- (* HavocProcess *)
  left. unfold step_ok. intros0 Hty Hr Hstep.
  invc Hstep; [on >db_step, invc | on >output_step, invc | | ].
  all: assumption.

Defined.


Definition check_step : forall dba rn op,
    MicroForall (step_ok dba rn) op + list error.
intros ? ?.
induction op using micro_rect_g with
    (Pl := fun ops => (Forall (MicroForall (step_ok dba rn)) ops + list error)%type).

all: try match goal with
| [ |- (MicroForall _ ?op + _)%type ] =>
        destruct (check_step' dba rn op); [ | die_auto ]
end.

(* flat opcodes - just use the proof we got from the check_step' call *)
all: try solve [ left; eapply MfOther; auto ].

- (* CalcCond *)
  destruct IHop; [ | die_auto ].
  left. constructor; auto.

- (* ScheduleCallback *)
  destruct IHop; [ | die_auto ].
  left. constructor; auto.

- (* nil *)
  left. constructor.

- (* cons *)
  destruct IHop; [ | die_auto ].
  destruct IHop0; [ | die_auto ].
  left. constructor; auto.
Defined.



Definition record_program_ok dba rn rp :=
    Forall (MicroForall (step_ok dba rn)) (rp_code rp).

Fixpoint database_program_ok' dba rn dbp :=
    match dbp with
    | [] => True
    | rp :: dbp => record_program_ok dba rn rp /\ database_program_ok' dba (S rn) dbp
    end.

Definition database_program_ok dba dbp :=
    database_program_ok' dba 0%nat dbp.


Definition check_record_program : forall dba rn rp,
    record_program_ok dba rn rp + list error.
intros. destruct rp. induction rp_code.

- left. constructor.

- rename a into op.
  destruct (check_step dba rn op) as [Hop | ?]; [ | die_auto ].
  destruct IHrp_code as [Hops | ?]; [ | die_auto ].
  left. constructor; assumption.
Defined.

Definition check_database_program' : forall dba rn dbp,
    database_program_ok' dba rn dbp + list error.
intros. generalize dependent rn. induction dbp; intros.

- left. exact I.

- rename a into rp.
  destruct (check_record_program dba rn rp); [ | die_auto ].
  destruct (IHdbp (S rn)); [ | die_auto ].
  left. split; assumption.
Defined.

Definition check_database_program : forall dba dbp,
    database_program_ok dba dbp + list error.
intros.
eapply check_database_program'.
Defined.




Open Scope nat_scope.

Lemma database_program_ok'_lookup : forall dba dbp rn_base rn rp,
    database_program_ok' dba rn_base dbp ->
    lookup dbp rn = Some rp ->
    record_program_ok dba (rn_base + rn)%nat rp.
first_induction dbp; intros0 Hok Hlook.
  { destruct rn; simpl in Hlook; discriminate. }
invc Hok. destruct rn.
  { simpl in *. inject_some.
    unfold record_name in rn_base.
    replace ((rn_base + 0)%nat) with rn_base by lia. assumption. }

specialize (IHdbp ?? ?? ?? ?? ** **).
replace (rn_base + S rn) with (S rn_base + rn) by lia. assumption.
Qed.

Lemma database_program_ok_lookup : forall dba dbp rn rp,
    database_program_ok dba dbp ->
    lookup dbp rn = Some rp ->
    record_program_ok dba rn rp.
intros. eapply database_program_ok'_lookup with (rn_base := 0); eauto.
Qed.

Theorem step_preserves_refine : forall dba dbp state state' oes,
    let dbt := database_program_type dbp in
    database_state_type (state_dbs state) = dbt ->
    database_abs_type dba = dbt ->
    CF.state_ok dbp state ->
    database_program_ok dba dbp ->
    refine dba (state_dbs state) ->
    step dbp state state' oes ->
    refine dba (state_dbs state').
intros0 Hdbs_ty Hdba_ty Hcontrol Hprog Hstate Hstep.

destruct state, state_stk; simpl in *.
  { invc Hstep. }

on >CF.state_ok, invc.
on >CF.frame_ok, invc.
forward eapply database_program_ok_lookup; eauto.
unfold record_program_ok in *.
forward eapply CF.suffix_forall; eauto.

destruct f. simpl in *.
destruct frame_code as [| op ?]; simpl in *.
  { (* pop *) invc Hstep. simpl. assumption. }
on (Forall _ (op :: _)), invc.
assert (Hok : step_ok dba frame_rn op) by (eapply forall_one; assumption).

unfold step_ok in Hok.
destruct state'. simpl in *.
eapply Hok; try exact Hstep; eauto. congruence.
Qed.

Theorem star_step_preserves_refine : forall dba dbp state state' oes,
    let dbt := database_program_type dbp in
    database_state_type (state_dbs state) = dbt ->
    database_abs_type dba = dbt ->
    CF.state_ok dbp state ->
    database_program_ok dba dbp ->
    refine dba (state_dbs state) ->
    star_step dbp state state' oes ->
    refine dba (state_dbs state').
induction 6.
- eauto using step_preserves_refine.
- eapply IHstar_step; eauto.
  + erewrite <- step_preserves_state_type by eassumption. assumption.
  + eauto using CF.step_state_ok.
  + eauto using step_preserves_refine.
Qed.



Definition float_abs_init (dbs : database_state) : database_abs :=
    database_state_abs dbs.

Definition float_abs_update dbp dba :=
    interp_prog dba dbp.

Definition float_abs_check dbp dba :=
    check_database_program dba dbp.

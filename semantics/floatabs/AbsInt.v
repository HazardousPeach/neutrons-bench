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
Require Import v1.FloatAux.

Require epics.ControlFlow.
Require Import epics.Opcodes.
Require Import epics.Preservation.
Require Import epics.Step.
Require Import epics.Types.
Require Import epics.Records.
Require Import epics.Wf.
Require expr.Dbl.
Require Import expr.Expr.
Require Import floatabs.Records.
Require Import floatabs.RecordData.
Require floatabs.AbsExpr.
Require Import floatabs.AbsExprProofs.
Require Import util.ListLemmas.


Set Default Timeout 10.
Set Implicit Arguments.
Open Scope Z.

Module ER.
    Include epics.SpecRecords.
    Include epics.SpecRecordData.
    Include epics.SpecRecordSetters.
End ER.

Module Abs.
    Include floatabs.Records.
    Include floatabs.RecordData.
End Abs.

Module ExprAbs := floatabs.AbsExpr.

Module CF := epics.ControlFlow.



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




Inductive refine_val : abs_value -> value -> Prop :=
| RvTop : forall v, refine_val None v
| RvDouble : forall d z min max,
        fwhole_eq d z ->
        (min <= z <= max)%Z ->
        refine_val (Some (min, max)) (VDouble d)
| RvEnum : forall z pf min max,
        (min <= z <= max)%Z ->
        refine_val (Some (min, max)) (VEnum (EEnum z pf))
| RvLong : forall z pf min max,
        (min <= z <= max)%Z ->
        refine_val (Some (min, max)) (VLong (ELong z pf))
.

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

Definition check_wider : forall a a',
    { wider a a' } + { ~ wider a a' }.
destruct a, a'; try solve [ right; inversion 1 | left; econstructor ].
- destruct p as [min1 max1], p0 as [min2 max2].
  destruct (Z_le_dec min2 min1); [ | right; inversion 1; lia ].
  destruct (Z_le_dec max1 max2); [ | right; inversion 1; lia ].
  left. constructor; assumption.
Qed.

Lemma wider_refl : forall a, wider a a.
destruct a; try constructor.
destruct p; try constructor; lia.
Qed.

Lemma wider_trans : forall a1 a2 a3,
    wider a1 a2 ->
    wider a2 a3 ->
    wider a1 a3.
intros0 Hw12 Hw23.
invc Hw12; invc Hw23; constructor; lia.
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
- econstructor. lia.
- econstructor. lia.
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
try discriminate Hwf.

all: destruct val; try discriminate Hwf.

all: cbv  [write_field bind_option unwrap_double unwrap_string unwrap_long unwrap_enum] in Hwf;
     try break_match; try discriminate;
     fancy_injr <- Hwf; destruct st;
     cbv -[multi_get multi_set];
     try rewrite multi_set_get; (* multi fields *)
     try reflexivity.

all: try solve [
    (* VArray handling *)
    simpl in *;
    do 2 (break_match; try discriminate);
    on (Some _ = Some _), invc; reflexivity
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
try discriminate Hwf.

all: cbv  [write_field bind_option unwrap_double unwrap_string unwrap_long unwrap_enum] in Hwf;
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
  eapply Forall2_nth_error; eauto. subst. assumption.
Qed.


Definition convert_abs (a : abs_value) (old_ty new_ty : field_type) : abs_value :=
    (* In general, if precise conversions exist for all values in `a`, then the
       result is `a`.  Otherwise, the conversion result is unconstrained, and
       we return `None`. *)
    match old_ty, new_ty with
    | TDouble, TDouble => a
    | TDouble, TEnum =>
            if check_wider a (Some (0, ENUM_MAX - 1)%Z) then a else None
    | TDouble, TLong =>
            if check_wider a (Some (-LONG_MAX, LONG_MAX - 1)%Z) then a else None
    | TDouble, _ => None

    | TEnum, TDouble => a
    | TEnum, TEnum => a
    | TEnum, TLong => a
    | TEnum, _ => None

    | TLong, TDouble => a
    | TLong, TEnum =>
            if check_wider a (Some (0, ENUM_MAX - 1)%Z) then a else None
    | TLong, TLong => a
    | TLong, _ => None

    | _, _ => None (* strings and arrays *)
    end.

Lemma convert_abs_top : forall old_ty new_ty,
    convert_abs None old_ty new_ty = None.
intros.
destruct old_ty, new_ty; simpl; try reflexivity.
all: break_match; reflexivity.
Qed.

Lemma convert_value_refine : forall v a ty v',
    refine_val a v ->
    convert_value v ty v' ->
    refine_val (convert_abs a (value_type v) ty) v'.
intros0 Hrv Hconv. invc Hrv.

- rewrite convert_abs_top. constructor.

- destruct ty; simpl; try constructor.
  all: try break_match; try constructor.
  all: unfold convert_value in Hconv; break_and.
  all: try on >wider, invc.
  all: rename H2 into Hconv.

  + subst. econstructor; eauto.

  + erewrite B2Z_safe_complete in * by eassumption.
    assert (0 <= z < ENUM_MAX). { unfold ENUM_MAX. lia. }
    rewrite (Hconv **).
    constructor. eauto.

  + erewrite B2Z_safe_complete in * by eassumption.
    assert (-LONG_MAX <= z < LONG_MAX). { unfold LONG_MAX. lia. }
    rewrite (Hconv **).
    constructor. eauto.

- destruct ty; simpl; try constructor.
  all: try break_match; try constructor.
  all: unfold convert_value in Hconv; break_and.
  all: try on >wider, invc.
  all: rename H1 into Hconv.

  + rewrite Hconv by lia.
    econstructor; eauto.
    eapply fwhole_eq_Z2B. rewrite Z.abs_lt.
    change (53 - 1) with 52.
    unfold ENUM_MAX in *.  lia.

  + rewrite Hconv.
    constructor; eauto.

  + rewrite Hconv.
    constructor; eauto.

- destruct ty; simpl; try constructor.
  all: try break_match; try constructor.
  all: unfold convert_value in Hconv; break_and.
  all: try on >wider, invc.
  all: rename H1 into Hconv.

  + rewrite Hconv by lia.
    econstructor; eauto.
    eapply fwhole_eq_Z2B. rewrite Z.abs_lt.
    change (53 - 1) with 52.
    unfold LONG_MAX in *.  lia.

  + rewrite (Hconv ltac:(unfold ENUM_MAX in *; lia)).
    constructor; eauto.

  + rewrite Hconv.
    constructor; eauto.

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

| EInOpcode : micro -> error -> error
| EInRecord : record_name -> error -> error
.

Definition in_context {A} (ctx : error -> error) (r : A + list error) : A + list error :=
    match r with
    | inl x => inl x
    | inr e => inr (map ctx e)
    end.


Ltac die x := right; exact x.
Ltac die_auto :=
    match goal with
    | [ e : list error |- _ ] => die e
    end.
Ltac die_ctx c :=
    match goal with
    | [ e : list error |- _ ] => apply (in_context c); die e
    end.

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

- destruct e. rename val into z.

  destruct p as [min max].
  destruct (Z_le_gt_dec min z); cycle 1.
    { right. inversion 1. lia. }
  destruct (Z_le_gt_dec z max); cycle 1.
    { right. inversion 1. lia. }

  left. econstructor. eauto.

- destruct e. rename val into z.

  destruct p as [min max].
  destruct (Z_le_gt_dec min z); cycle 1.
    { right. inversion 1. lia. }
  destruct (Z_le_gt_dec z max); cycle 1.
    { right. inversion 1. lia. }

  left. econstructor. eauto.
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
set (conv_abs := convert_abs src_abs src_ty dest_ty).
destruct (check_wider conv_abs dest_abs); [ | die [ENotWider conv_abs dest_abs] ].

left. unfold db_step_ok. intros0 Hty Hr Hstep. invc Hstep.
eapply write_record_field_refine; try eassumption.
eapply refine_val_wider; try eassumption.
eapply convert_value_refine; eauto.
eapply read_record_field_refine; try eassumption.
Defined.

Definition check_read_link : forall dba rn il il_ty fn f_ty,
    db_step_ok dba rn (MReadLink il il_ty fn f_ty) + list error.
intros.
destruct (lookup dba rn) as [ra | ] eqn:?; [ | die [ENoRecord rn] ].
destruct (lookup dba (fl_rn il)) as [ra' | ] eqn:?; [ | die [ENoRecord (fl_rn il)] ].
destruct (Abs.read_field ra' (fl_fn il)) as [src_abs | ] eqn:?; [ | die [ENoField (fl_fn il)] ].
destruct (Abs.read_field ra fn) as [dest_abs | ] eqn:?; [ | die [ENoField fn] ].
set (conv_abs := convert_abs src_abs il_ty f_ty).
destruct (check_wider conv_abs dest_abs); [ | die [ENotWider conv_abs dest_abs] ].

left. unfold db_step_ok. intros0 Hty Hr Hstep. invc Hstep.
eapply write_record_field_refine; try eassumption.
eapply refine_val_wider; try eassumption.
eapply convert_value_refine; eauto.
eapply read_record_field_refine; try eassumption.
Defined.

Definition check_write_link : forall dba rn fn f_ty ol ol_ty,
    db_step_ok dba rn (MWriteLink fn f_ty ol ol_ty) + list error.
intros.
destruct (lookup dba rn) as [ra | ] eqn:?; [ | die [ENoRecord rn] ].
destruct (lookup dba (fl_rn ol)) as [ra' | ] eqn:?; [ | die [ENoRecord (fl_rn ol)] ].
destruct (Abs.read_field ra fn) as [src_abs | ] eqn:?; [ | die [ENoField fn] ].
destruct (Abs.read_field ra' (fl_fn ol)) as [dest_abs | ] eqn:?; [ | die [ENoField (fl_fn ol)] ].
set (conv_abs := convert_abs src_abs f_ty ol_ty).
destruct (check_wider conv_abs dest_abs); [ | die [ENotWider conv_abs dest_abs] ].

left. unfold db_step_ok. intros0 Hty Hr Hstep. invc Hstep.
eapply write_record_field_refine; try eassumption.
eapply refine_val_wider; try eassumption.
eapply convert_value_refine; eauto.
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
    | RsCalc st => Some (ER.calc_A_to_L st)
    | RsCalcOut st => Some (ER.calc_out_A_to_L st)
    | _ => None
    end.

Definition abs_A_to_L a :=
    match a with
    | RaCalc abs => Some (Abs.calc_A_to_L abs)
    | RaCalcOut abs => Some (Abs.calc_out_A_to_L abs)
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
        return ty_denote floatabs.AbsExprProofs.D dty_ ->
               ty_denote floatabs.AbsExprProofs.A aty_ -> Prop with
    | expr.Dbl.Nil, ExprAbs.Nil => fun dbl abs => True
    | expr.Dbl.Dbl, ExprAbs.Abs => fun dbl abs => refine_val abs (VDouble dbl)
    | _, _ => fun dbl abs => False
    end) dbl abs <->
    floatabs.AbsExprProofs.refine_value dty aty dbl abs.
intros. split; intro HH.
- destruct dty, aty; try solve [exfalso; auto].
  + destruct dbl, abs. constructor.
  + invc HH; do 2 econstructor; eauto.
- destruct HH; auto.
  on >floatabs.AbsExprProofs.refine_dbl, invc.
  all: econstructor; eauto.
Qed.

Lemma refine_val_double_iff : forall dbl abs,
    refine_val abs (VDouble dbl) <->
    floatabs.AbsExprProofs.refine_value expr.Dbl.Dbl ExprAbs.Abs dbl abs.
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
    MForall2 (floatabs.AbsExprProofs.refine_value expr.Dbl.Dbl ExprAbs.Abs) sa2l aa2l.
intros. forward eapply refine_record_A_to_L; eauto.
rewrite -> MForall2_Forall2 in *.
compute -[multi_to_list e_double abs_value]. (* modifies implicit arguments *)
remember (multi_to_list sa2l) as sa2l'.
remember (multi_to_list aa2l) as aa2l'.
try rewrite <- Heqaa2l' in *.
(* `remember` should do this, but there's an issue with the implicits in 8.5pl1 *)
list_magic_on (sa2l', (aa2l', tt)).
rewrite <- refine_val_double_iff. auto.
Qed.

Definition is_A_to_L_dec : forall fn,
    { i | fn = f_A_to_L i } + { ~ exists i, fn = f_A_to_L i }.
destruct fn; try solve [ right; inversion 1; discriminate ].
left; eauto.
Defined.

Lemma run_calculate_record_refine : forall expr f f' fn_out rs rs' ra a2l a2l' out out',
    expr.Dbl.denote expr = Some f ->
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

forward eapply floatabs.AbsExprProofs.denote_refine as HH; eauto.
  destruct HH as (f'' & ? & ?).
  replace f'' with f' in * by congruence.
forward refine (floatabs.AbsExprProofs.refine_state_fn_noxvar_dbl_abs_inv _ _ _)
    as Hfrel; eauto.
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

Timeout 20 Qed.


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

Definition check_hw_read : forall dba rn fn f_ty,
    db_step_ok dba rn (MHwRead fn f_ty) + list error.
intros.
destruct (lookup dba rn) as [ra | ] eqn:?; [ | die [ENoRecord rn] ].
destruct (Abs.read_field ra fn) as [dest_abs | ] eqn:?; [ | die [ENoField fn] ].
destruct (check_wider None dest_abs); [ | die [ENotWider None dest_abs] ].

left. unfold db_step_ok. intros0 Hty Hr Hstep. invc Hstep.
eapply write_record_field_refine; try eassumption.
eapply refine_val_wider; try eassumption.
constructor.
Defined.

Definition check_unk_read : forall dba rn fn f_ty,
    db_step_ok dba rn (MUnkRead fn f_ty) + list error.
intros.
destruct (lookup dba rn) as [ra | ] eqn:?; [ | die [ENoRecord rn] ].
destruct (Abs.read_field ra fn) as [dest_abs | ] eqn:?; [ | die [ENoField fn] ].
destruct (check_wider None dest_abs); [ | die [ENotWider None dest_abs] ].

left. unfold db_step_ok. intros0 Hty Hr Hstep. invc Hstep.
eapply write_record_field_refine; try eassumption.
eapply refine_val_wider; try eassumption.
constructor.
Defined.

Definition check_unk_write : forall dba rn,
    db_step_ok dba rn (MUnkWrite) + list error.
intros.

left. unfold db_step_ok. intros0 Hty Hr Hstep. invc Hstep.
assumption.
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


Lemma read_field_has_field : forall ra fn abs,
    Abs.read_field ra fn = Some abs ->
    exists ty, record_has_field (record_abs_type ra) fn ty.
destruct fn, ra; intros0 Hrf; try discriminate Hrf.
all: eexists; constructor; reflexivity.
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
- eapply check_hw_read.
- eapply check_unk_read.
- eapply check_unk_write.
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
eapply (in_context (EInRecord rn)).
eapply (in_context (EInOpcode op)).
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
induction op using micro_rect_mut with
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
  destruct (check_step dba rn op) as [Hop | errs1];
  destruct IHrp_code as [Hops | errs2].
  + left. constructor; assumption.
  + right; exact errs2.
  + right; exact errs1.
  + right; exact (errs1 ++ errs2).
Defined.

Definition check_database_program' : forall dba rn dbp,
    database_program_ok' dba rn dbp + list error.
intros. generalize dependent rn. induction dbp; intros.

- left. exact I.

- rename a into rp.
  destruct (check_record_program dba rn rp) as [Hr | errs1];
  destruct (IHdbp (S rn)) as [Hrs | errs2].
  + left. split; assumption.
  + right; exact errs2.
  + right; exact errs1.
  + right; exact (errs1 ++ errs2).
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



Definition float_abs_check dbp dba :=
    check_database_program dba dbp.

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
Require v1.ExprAbs.

Require Import v1.EpicsTypes.
Require Import v1.FloatAux.
Require Import v1.FloatAbs.
Require Import v1.FloatAbsBase.
Require Import v1.Step.
Require Import v1.StepAux.
Require v1.ControlFlow.

Set Default Timeout 10.

Module Dbl := ExprDbl.
Module Abs := ExprAbs.



Definition D := Dbl.dbl_eval_bits.
Definition A := Abs.abs_eval_bits.

Inductive ty_rel : Dbl.dbl_tydesc -> Abs.abs_tydesc -> Prop :=
| TrNil : ty_rel Dbl.Nil Abs.Nil
| TrDbl : ty_rel Dbl.Dbl Abs.Abs
.
Hint Constructors ty_rel.


Definition lift (fd : tydesc D -> Type) (fa : tydesc A -> Type) :
    (forall dty aty, fd dty -> fa aty -> Prop) ->
    ({ ty : tydesc D & fd ty } -> { ty : tydesc A & fa ty } -> Prop).
intro P.
intros dsig asig.
destruct dsig as [d d'], asig as [a a'].
eapply P; eassumption.
Defined.


Inductive refine_dbl : e_double -> abs_value -> Prop :=
| RdNone : forall d, refine_dbl d None
| RdSome : forall d z min max,
        fwhole_eq d z ->
        (min <= z <= max)%Z ->
        refine_dbl d (Some (min, max)).

Inductive refine_value : forall dty aty, ty_denote D dty -> ty_denote A aty -> Prop :=
| RvNil : refine_value Dbl.Nil Abs.Nil tt tt
| RvDbl : forall d a,
        refine_dbl d a ->
        refine_value Dbl.Dbl Abs.Abs d a.
Definition refine_value' :
    ({ ty : tydesc D & ty_denote D ty } -> { ty : tydesc A & ty_denote A ty } -> Prop) :=
    lift _ _ refine_value.

Inductive refine_unop dty1 aty1 :
    forall dtyR atyR
        (df : unop_impl _ dty1 dtyR)
        (af : unop_impl _ aty1 atyR),
        Prop :=
| RefineUnop : forall dtyR atyR df af,
    ty_rel dty1 aty1 ->
    ty_rel dtyR atyR ->
    (forall dx1 ax1,
        refine_value dty1 aty1 dx1 ax1 ->
        refine_value dtyR atyR (df dx1) (af ax1)) ->
    refine_unop dty1 aty1 dtyR atyR df af.
Definition refine_unop' dty1 aty1 :=
    lift _ _ (refine_unop dty1 aty1).

Inductive refine_binop dty1 aty1 dty2 aty2 :
    forall dtyR atyR
        (df : binop_impl _ dty1 dty2 dtyR)
        (af : binop_impl _ aty1 aty2 atyR),
        Prop :=
| RefineBinop : forall dtyR atyR df af,
    ty_rel dty1 aty1 ->
    ty_rel dty2 aty2 ->
    ty_rel dtyR atyR ->
    (forall dx1 ax1 dx2 ax2,
        refine_value dty1 aty1 dx1 ax1 ->
        refine_value dty2 aty2 dx2 ax2 ->
        refine_value dtyR atyR (df dx1 dx2) (af ax1 ax2)) ->
    refine_binop dty1 aty1 dty2 aty2 dtyR atyR df af.
Definition refine_binop' dty1 aty1 dty2 aty2 :=
    lift _ _ (refine_binop dty1 aty1 dty2 aty2).

Inductive refine_ternop dty1 aty1 dty2 aty2 dty3 aty3 :
    forall dtyR atyR
        (df : ternop_impl _ dty1 dty2 dty3 dtyR)
        (af : ternop_impl _ aty1 aty2 aty3 atyR),
        Prop :=
| RefineTernop : forall dtyR atyR df af,
    ty_rel dty1 aty1 ->
    ty_rel dty2 aty2 ->
    ty_rel dty3 aty3 ->
    ty_rel dtyR atyR ->
    (forall dx1 ax1 dx2 ax2 dx3 ax3,
        refine_value dty1 aty1 dx1 ax1 ->
        refine_value dty2 aty2 dx2 ax2 ->
        refine_value dty3 aty3 dx3 ax3 ->
        refine_value dtyR atyR (df dx1 dx2 dx3) (af ax1 ax2 ax3)) ->
    refine_ternop dty1 aty1 dty2 aty2 dty3 aty3 dtyR atyR df af.
Definition refine_ternop' dty1 aty1 dty2 aty2 dty3 aty3 :=
    lift _ _ (refine_ternop dty1 aty1 dty2 aty2 dty3 aty3).

Inductive refine_varop dty1 aty1 :
    forall dtyR atyR
        (df : varop_impl _ dty1 dtyR)
        (af : varop_impl _ aty1 atyR),
        Prop :=
| RefineVarop : forall dtyR atyR df af,
    ty_rel dty1 aty1 ->
    ty_rel dtyR atyR ->
    (forall dx1 ax1,
        Forall2 (refine_value dty1 aty1) dx1 ax1 ->
        refine_value dtyR atyR (df dx1) (af ax1)) ->
    refine_varop dty1 aty1 dtyR atyR df af.
Definition refine_varop' dty1 aty1 :=
    lift _ _ (refine_varop dty1 aty1).

Inductive refine_state_fn :
    forall dtyR atyR
        (df : state_fn D 12 (ty_denote D dtyR))
        (af : state_fn A 12 (ty_denote A atyR)),
        Prop :=
| RefineStateFn : forall dtyR atyR df af,
    ty_rel dtyR atyR ->
    (forall dsv dsx asv asx dsv' dsx' dr asv' asx' ar,
        MForall2 (refine_value _ _) dsv asv ->
        MForall2 (refine_value _ _) dsx asx ->
        df dsv dsx = (dsv', dsx', dr) ->
        af asv asx = (asv', asx', ar) ->
        MForall2 (refine_value _ _) dsv' asv' /\
        MForall2 (refine_value _ _) dsx' asx' /\
        refine_value _ _ dr ar) ->
    refine_state_fn dtyR atyR df af.
Definition refine_state_fn' :=
    lift _ _ (refine_state_fn).

Inductive refine_state_fn_list :
    forall dtyR atyR
        (df : state_fn D 12 (list (ty_denote D dtyR)))
        (af : state_fn A 12 (list (ty_denote A atyR))),
        Prop :=
| RefineStateFnList : forall dtyR atyR df af,
    ty_rel dtyR atyR ->
    (forall dsv dsx asv asx dsv' dsx' drs asv' asx' ars,
        MForall2 (refine_value _ _) dsv asv ->
        MForall2 (refine_value _ _) dsx asx ->
        df dsv dsx = (dsv', dsx', drs) ->
        af asv asx = (asv', asx', ars) ->
        MForall2 (refine_value _ _) dsv' asv' /\
        MForall2 (refine_value _ _) dsx' asx' /\
        Forall2 (refine_value _ _) drs ars) ->
    refine_state_fn_list dtyR atyR df af.
Definition refine_state_fn_list' :=
    lift _ _ (refine_state_fn_list).

Inductive refine_state_fn_noxvar :
    forall dtyR atyR
        (df : state_fn_noxvar D 12 (ty_denote D dtyR))
        (af : state_fn_noxvar A 12 (ty_denote A atyR)),
        Prop :=
| RefineStateFnNoXVar : forall dtyR atyR df af,
    ty_rel dtyR atyR ->
    (forall dsv asv dsv' dr asv' ar,
        MForall2 (refine_value _ _) dsv asv ->
        df dsv = (dsv', dr) ->
        af asv = (asv', ar) ->
        MForall2 (refine_value _ _) dsv' asv' /\
        refine_value _ _ dr ar) ->
    refine_state_fn_noxvar dtyR atyR df af.
Definition refine_state_fn_noxvar' :=
    lift _ _ (refine_state_fn_noxvar).


Lemma double_abs_refine : forall d,
    refine_dbl d (Abs.double_abs d).
intros. unfold Abs.double_abs. break_match.
- econstructor.
  + eapply B2Z_safe_correct. eassumption.
  + omega.
- constructor.
Qed.

Lemma convert_lit_refine : forall x,
    refine_value' (convert_lit D x) (convert_lit A x).
intros. simpl.  constructor. eauto using double_abs_refine.
Qed.

Local Hint Resolve (tydesc_eq_dec D) : eq_dec.
Local Hint Resolve (tydesc_eq_dec A) : eq_dec.



Lemma abs_bool_refine : forall d,
    (d = zero \/ d = one) ->
    refine_dbl d Abs.abs_bool.
intros0 Hor. destruct Hor.
- econstructor.
  + subst. eapply fwhole_eq_Z2B.
    eapply Z.pow_pos_nonneg; omega.
  + omega.

- econstructor.
  + subst. eapply fwhole_eq_Z2B.
    rewrite Z.abs_eq by omega.
    replace 1 with (1 ^ (53 - 1)) at 1 by (eapply Z.pow_1_l; omega).
    eapply Z.pow_lt_mono_l; omega.
  + omega.
Qed.

Lemma unop_denote_refine : forall op dty1 aty1 dden,
    ty_rel dty1 aty1 ->
    unop_denote D op dty1 = Some dden ->
    exists aden,
        unop_denote A op aty1 = Some aden /\
        refine_unop' _ _ dden aden.
destruct op, dty1; inversion 1; intros0 Dop;
simpl in *; try discriminate.
all: eexists; split; [ reflexivity | ].
all: inject_some; unfold refine_unop', lift.
all: constructor; eauto.
all: inversion 1; constructor.
all: fix_existT; subst.

- on >refine_dbl, invc; [ solve [constructor] | ].
  simpl. unfold Abs.check_overflow. do 2 (break_if; try solve [constructor]).
  econstructor.
  + eapply fwhole_eq_Bopp; eauto.
  + omega.

- eapply abs_bool_refine.  break_if; eauto.

Qed.


Lemma Z_mult_range_max_l : forall x y0 y1 y,
    y0 <= y <= y1 ->
    x * y <= Z.max (x * y0) (x * y1).
intros. destruct (Z_le_gt_dec 0 x).
- eapply Z.le_trans with (m := x * y1).
  + eapply Z.mul_le_mono_nonneg_l; omega.
  + eapply Z.le_max_r.
- eapply Z.le_trans with (m := x * y0).
  + eapply Z.mul_le_mono_nonpos_l; omega.
  + eapply Z.le_max_l.
Qed.

Lemma Z_mult_range_max_r : forall x0 x1 x y,
    x0 <= x <= x1 ->
    x * y <= Z.max (x0 * y) (x1 * y).
intros. destruct (Z_le_gt_dec 0 y).
- eapply Z.le_trans with (m := x1 * y).
  + eapply Z.mul_le_mono_nonneg_r; omega.
  + eapply Z.le_max_r.
- eapply Z.le_trans with (m := x0 * y).
  + eapply Z.mul_le_mono_nonpos_r; omega.
  + eapply Z.le_max_l.
Qed.

Lemma Z_mult_range_max : forall x0 x1 y0 y1 x y,
    x0 <= x <= x1 ->
    y0 <= y <= y1 ->
    let z1 := Z.max (Z.max (x0 * y0) (x0 * y1)) (Z.max (x1 * y0) (x1 * y1)) in
    x * y <= z1.
intros.
eapply Z.le_trans with (m := Z.max (x0 * y) (x1 * y)).
- eapply Z_mult_range_max_r. eauto.
- eapply Z.max_le_compat; eapply Z_mult_range_max_l; eauto.
Qed.


Lemma Z_mult_range_min_l : forall x y0 y1 y,
    y0 <= y <= y1 ->
    Z.min (x * y0) (x * y1) <= x * y.
intros. destruct (Z_le_gt_dec 0 x).
- eapply Z.le_trans with (m := x * y0).
  + eapply Z.le_min_l.
  + eapply Z.mul_le_mono_nonneg_l; omega.
- eapply Z.le_trans with (m := x * y1).
  + eapply Z.le_min_r.
  + eapply Z.mul_le_mono_nonpos_l; omega.
Qed.

Lemma Z_mult_range_min_r : forall x0 x1 x y,
    x0 <= x <= x1 ->
    Z.min (x0 * y) (x1 * y) <= x * y.
intros. destruct (Z_le_gt_dec 0 y).
- eapply Z.le_trans with (m := x0 * y).
  + eapply Z.le_min_l.
  + eapply Z.mul_le_mono_nonneg_r; omega.
- eapply Z.le_trans with (m := x1 * y).
  + eapply Z.le_min_r.
  + eapply Z.mul_le_mono_nonpos_r; omega.
Qed.

Lemma Z_mult_range_min : forall x0 x1 y0 y1 x y,
    x0 <= x <= x1 ->
    y0 <= y <= y1 ->
    let z0 := Z.min (Z.min (x0 * y0) (x0 * y1)) (Z.min (x1 * y0) (x1 * y1)) in
    z0 <= x * y.
intros.
eapply Z.le_trans with (m := Z.min (x0 * y) (x1 * y)).
- eapply Z.min_le_compat; eapply Z_mult_range_min_l; eauto.
- eapply Z_mult_range_min_r. eauto.
Qed.


Lemma Z_mult_range : forall x0 x1 y0 y1 x y,
    x0 <= x <= x1 ->
    y0 <= y <= y1 ->
    let z0 := Z.min (Z.min (x0 * y0) (x0 * y1)) (Z.min (x1 * y0) (x1 * y1)) in
    let z1 := Z.max (Z.max (x0 * y0) (x0 * y1)) (Z.max (x1 * y0) (x1 * y1)) in
    z0 <= x * y <= z1.
intros. split; eauto using Z_mult_range_min, Z_mult_range_max.
Qed.


Lemma binop_denote_refine : forall op dty1 aty1 dty2 aty2 dden,
    ty_rel dty1 aty1 ->
    ty_rel dty2 aty2 ->
    binop_denote D op dty1 dty2 = Some dden ->
    exists aden,
        binop_denote A op aty1 aty2 = Some aden /\
        refine_binop' _ _ _ _ dden aden.
destruct op, dty1, dty2; do 2 inversion 1; intros0 Dop;
simpl in *; try discriminate.
all: eexists; split; [ reflexivity | ].
all: inject_some; unfold refine_unop', lift.
all: constructor; eauto.
all: do 2 inversion 1; constructor.
all: fix_existT; subst.

- do 2 (on >refine_dbl, invc; [ solve [constructor] | ]).
  simpl. unfold Abs.check_overflow. do 2 (break_if; try solve [constructor]).
  econstructor.
  + eapply fwhole_eq_Bplus; eauto.
    rewrite Z_abs_range. change (53 - 1) with 52. omega.
  + omega.

- do 2 (on >refine_dbl, invc; [ solve [constructor] | ]).
  simpl. unfold Abs.check_overflow. do 2 (break_if; try solve [constructor]).
  econstructor.
  + eapply fwhole_eq_Bminus; eauto.
    rewrite Z_abs_range. change (53 - 1) with 52. omega.
  + omega.

- do 2 (on >refine_dbl, invc; [ solve [constructor] | ]).
  simpl. unfold Abs.check_overflow. do 2 (break_if; try solve [constructor]).
  econstructor.
  + eapply fwhole_eq_Bmult; eauto.
    rewrite Z_abs_range. change (53 - 1) with 52.
    forward eapply Z_mult_range with (x := z) (y := z0); eauto.
    cbv zeta in *. omega.
  + eapply Z_mult_range; eauto.

- constructor.

- eapply abs_bool_refine.  unfold Dbl.b64_ge. do 2 (break_match; eauto).
- eapply abs_bool_refine.  unfold Dbl.b64_gt. do 2 (break_match; eauto).
- eapply abs_bool_refine.  unfold Dbl.b64_le. do 2 (break_match; eauto).
- eapply abs_bool_refine.  unfold Dbl.b64_lt. do 2 (break_match; eauto).
- eapply abs_bool_refine.  unfold Dbl.b64_ne. do 2 (break_match; eauto).
- eapply abs_bool_refine.  unfold Dbl.b64_eq. do 2 (break_match; eauto).

- eapply abs_bool_refine.  unfold Dbl.b64_and. do 2 (break_if; eauto).
- eapply abs_bool_refine.  unfold Dbl.b64_or. do 2 (break_if; eauto).

Qed.


Lemma ternop_denote_refine : forall op dty1 aty1 dty2 aty2 dty3 aty3 dden,
    ty_rel dty1 aty1 ->
    ty_rel dty2 aty2 ->
    ty_rel dty3 aty3 ->
    ternop_denote D op dty1 dty2 dty3 = Some dden ->
    exists aden,
        ternop_denote A op aty1 aty2 aty3 = Some aden /\
        refine_ternop' _ _ _ _ _ _ dden aden.
destruct op, dty1, dty2, dty3; do 3 inversion 1; intros0 Dop;
simpl in *; try discriminate.
all: eexists; split; [ reflexivity | ].
all: inject_some; unfold refine_unop', lift.
all: constructor; eauto.
all: do 3 inversion 1; constructor.
all: fix_existT; subst.

- on (refine_dbl dx2 _), invc; [ solve [constructor] | ].
  on (refine_dbl dx3 _), invc; [ solve [constructor] | ].
  simpl. unfold Abs.check_overflow. do 3 (break_if; try solve [constructor]).
  + econstructor; eauto. lia.
  + econstructor; eauto. lia.

Qed.



Lemma min_fwhole_eq : forall dx dy zx zy,
    fwhole_eq dx zx ->
    fwhole_eq dy zy ->
    fwhole_eq (Dbl.b64_min dx dy) (Z.min zx zy).
intros0 Hx Hy.
unfold Dbl.b64_min, Z.min. break_match; [ break_match | ].
all: erewrite fwhole_eq_Bcompare in * by eauto.
4: discriminate.
all: inject_some; find_rewrite.
all: eauto.

(* Eq case needs a bit more. *)
rewrite Z.compare_eq_iff in *. subst. auto.
Qed.

Lemma max_fwhole_eq : forall dx dy zx zy,
    fwhole_eq dx zx ->
    fwhole_eq dy zy ->
    fwhole_eq (Dbl.b64_max dx dy) (Z.max zx zy).
intros0 Hx Hy.
unfold Dbl.b64_max, Z.max. break_match; [ break_match | ].
all: erewrite fwhole_eq_Bcompare in * by eauto.
4: discriminate.
all: inject_some; find_rewrite.
all: eauto.
Qed.

Lemma min_refine : forall dx dy ax ay,
    refine_dbl dx ax ->
    refine_dbl dy ay ->
    refine_dbl (Dbl.b64_min dx dy) (Abs.abs_min ax ay).
intros0 Hx Hy.
invc Hx; invc Hy; simpl; try solve [constructor].
unfold Abs.check_overflow. do 2 (break_if; try solve [constructor]).
eapply RdSome with (z := Z.min z z0).
- eapply min_fwhole_eq; eauto.
- lia.
Qed.

Lemma max_refine : forall dx dy ax ay,
    refine_dbl dx ax ->
    refine_dbl dy ay ->
    refine_dbl (Dbl.b64_max dx dy) (Abs.abs_max ax ay).
intros0 Hx Hy.
invc Hx; invc Hy; simpl; try solve [constructor].
unfold Abs.check_overflow. do 2 (break_if; try solve [constructor]).
eapply RdSome with (z := Z.max z z0).
- eapply max_fwhole_eq; eauto.
- lia.
Qed.

Lemma minimum_refine : forall dxs axs,
    Forall2 refine_dbl dxs axs ->
    refine_dbl (Dbl.b64_minimum dxs) (Abs.abs_minimum axs).
induction dxs; intros0 Hfa; invc Hfa; simpl.
- eapply RdSome with (z := 0).
  + unfold zero. eapply fwhole_eq_Z2B. eapply Z.pow_pos_nonneg; lia.
  + lia.
- eapply min_refine; eauto.
Qed.

Lemma maximum_refine : forall dxs axs,
    Forall2 refine_dbl dxs axs ->
    refine_dbl (Dbl.b64_maximum dxs) (Abs.abs_maximum axs).
induction dxs; intros0 Hfa; invc Hfa; simpl.
2: on >Forall2, invc.
- eapply RdSome with (z := 0).
  + unfold zero. eapply fwhole_eq_Z2B. eapply Z.pow_pos_nonneg; lia.
  + lia.
- auto.
- eapply max_refine; eauto.
Qed.


Lemma refine_value_dbl : forall dx ax,
    refine_value Dbl.Dbl Abs.Abs dx ax <->
    refine_dbl dx ax.
intros. split; intro Hr.
- inversion Hr. fix_existT. subst. auto.
- constructor. auto.
Qed.

Lemma refine_value_dbl_list : forall dx ax,
    Forall2 (refine_value Dbl.Dbl Abs.Abs) dx ax <->
    Forall2 refine_dbl dx ax.
induction dx; intros; split; intro Hr; invc Hr; eauto.
- rewrite refine_value_dbl in *. rewrite IHdx in *. eauto.
- rewrite <- refine_value_dbl in *. rewrite <- IHdx in *. eauto.
Qed.

Lemma varop_denote_refine : forall op dty1 aty1 dden,
    ty_rel dty1 aty1 ->
    varop_denote D op dty1 = Some dden ->
    exists aden,
        varop_denote A op aty1 = Some aden /\
        refine_varop' _ _ dden aden.

destruct op, dty1; inversion 1; intros0 Dop;
simpl in *; try discriminate.
all: eexists; split; [ reflexivity | ].
all: inject_some; unfold refine_varop', lift.
all: constructor; eauto.
all: constructor.

- rewrite refine_value_dbl_list in *.
  eapply minimum_refine; eauto.

- rewrite refine_value_dbl_list in *.
  eapply maximum_refine; eauto.
Qed.


Ltac specialize_refinement :=
    repeat match goal with
    (* First, try to destruct some applications.  This will fail if the arguments
       used in the LHS have not been filled in yet, and we will fall through to the
       spec_evar case below. *)
    | [ H : forall x, _ |- _ ] =>
            match type of H with
            | context [ ?x = (_, _, _) ] =>
                    match x with
                    | (_, _, _) => fail 1
                    | _ => destruct x as [[? ?] ?] eqn:?
                    end
            end
    (* Main case: try to fill in arguments using evar or eassumption *)
    | [ H : forall x : ?T, _ |- _ ] =>
            match type of T with
            | Set => spec_evar H
            | Prop => 
                    match goal with
                    | [ H' : _ |- _ ] => specialize (H H'); clear H'
                    end
            end
    (* Also handle @eq premises with reflexivity *)
    | [ H : _ = _ -> _ |- _ ] => spec H by reflexivity
    (* Final cleanup: break `exists` and `and`. *)
    | [ H : exists _, _ |- _ ] => destruct H
    | [ H : _ /\ _ |- _ ] => destruct H
    end.

Lemma var_ty_rel : ty_rel (var_ty D) (var_ty A).
constructor.
Qed.

Lemma xvar_ty_rel : ty_rel (xvar_ty D) (xvar_ty A).
constructor.
Qed.

Lemma nil_ty_rel : ty_rel (nil_ty D) (nil_ty A).
constructor.
Qed.

Lemma ty_rel_inj : forall dty aty1 aty2,
    ty_rel dty aty1 ->
    ty_rel dty aty2 ->
    aty1 = aty2.
do 2 inversion 1; eauto.
Qed.

Lemma ty_rel_nil_sur : forall dty1 dty2,
    ty_rel dty1 (nil_ty A) ->
    ty_rel dty2 (nil_ty A) ->
    dty1 = dty2.
do 2 inversion 1; eauto.
Qed.

Lemma nil_rel_fwd : forall aty,
    ty_rel (nil_ty D) aty ->
    aty = nil_ty A.
intros. eapply ty_rel_inj; eauto using nil_ty_rel.
Qed.

Lemma nil_rel_rev : forall dty,
    ty_rel dty (nil_ty A) ->
    dty = nil_ty D.
intros. eapply ty_rel_nil_sur; eauto using nil_ty_rel.
Qed.


Lemma unpack_opt_helper1
    DI DP DR dopt (didx : DI) dval df drhs
    AI AP AR aopt (aidx : AI) aval af
        (P : AR -> Prop):
    unpack_opt (R := DR) dopt df = Some drhs ->
    dopt = Some (existT DP didx dval) ->
    aopt = Some (existT AP aidx aval) ->
    (df didx dval = Some drhs ->
        exists arhs, af aidx aval = Some arhs /\ P arhs) ->
    exists arhs, unpack_opt (R := AR) aopt af = Some arhs /\ P arhs.
intros0 Hunpack Hdden Haden Hinner.
subst dopt aopt. simpl in *.
eauto.
Qed.

Lemma unpack_opt_some_inv : forall I P R (opt : option { x : I & P x }) f rhs
        (Q : Prop),
    (forall idx val,
        opt = Some (existT P idx val) ->
        f idx val = Some rhs ->
        Q) ->
    unpack_opt (R := R) opt f = Some rhs -> Q.
intros.
destruct opt as [ s | ]; try discriminate.
destruct s. eauto.
Qed.

Lemma unpack_opt_some_inv' : forall I P R (opt : option { x : I & P x }) f rhs
        (Q : Prop),
    (forall idx val,
        opt = Some (existT P idx val) ->
        Q) ->
    unpack_opt (R := R) opt f = Some rhs -> Q.
inversion 2 using unpack_opt_some_inv. eauto.
Qed.

Lemma unpack_opt_some_ex
    I P R opt (idx : I) val f (Q : R -> Prop):
    opt = Some (existT P idx val) ->
    (exists rhs, f idx val = Some rhs /\ Q rhs) ->
    (exists rhs, unpack_opt (R := R) opt f = Some rhs /\ Q rhs).
intros0 Hopt Hinner.
subst opt. simpl in *. eauto.
Qed.

Ltac handle_unpack_opt :=
    let dden' := fresh "dden'" in
    let aden' := fresh "aden'" in
    let Hdden := fresh "Hdden" in
    let Haden := fresh "Haden" in
    let dty := fresh "dty" in
    let aty := fresh "aty" in
    let Hex := fresh "Hex" in
    let Hrefine := fresh "Hrefine" in

    match goal with
    | [ H : unpack_opt ?dden ?df = Some _ |-
        exists aden', unpack_opt ?aden ?af = Some _ /\ _ ] =>

            eapply unpack_opt_some_inv with (2 := H); clear H;
            intros dty dden' Hdden H;

            simple refine (let Hex : exists aden', aden = Some aden' /\ _ aden' := _ in _);
            [ shelve
            | eauto (* or defer to caller *)
            | clearbody Hex;
              destruct Hex as (aden' & Haden & Hrefine);
              destruct aden' as [aty aden'];
              eapply unpack_opt_some_ex; simpl in *; eauto
            ]
    end.


Lemma if_tydesc_eq_dec_inv : forall
    (T : Set) (A : eval_bits T)
    (P : tydesc A -> tydesc A -> Type)
    (ty xty : tydesc A)
    (x : forall ty xty, P ty xty)
    (y : forall ty xty, P ty xty)
    (z : forall ty xty, P ty xty)
    (Q : tydesc A -> Prop),
    (x xty xty = z xty xty -> Q xty) ->
    (ty <> xty ->
        y ty xty = z ty xty ->
        Q ty) ->
    ((if tydesc_eq_dec A ty xty then x ty xty else y ty xty) = z ty xty) -> Q ty.
intros.
destruct (tydesc_eq_dec _ _ _).
- subst. eauto.
- eauto.
Qed.

Lemma if_tydesc_eq_dec_eq_ex : forall
    (T : Set) (A : eval_bits T)
    (ty xty : tydesc A)
    (R : Type) (f g : tydesc A -> tydesc A -> option R)
    (Q : R -> Prop),
    ty = xty ->
    (exists rhs, f xty xty = Some rhs /\ Q rhs) ->
    (exists rhs, (if tydesc_eq_dec A ty xty then f ty xty else g ty xty) = Some rhs /\ Q rhs).
intros.
destruct (tydesc_eq_dec _ _ _); [ | exfalso; congruence ].
subst. auto.
Qed.

Lemma if_tydesc_eq_dec_ne_ex : forall
    (T : Set) (A : eval_bits T)
    (ty xty : tydesc A)
    (R : Type) (f g : tydesc A -> tydesc A -> option R)
    (Q : R -> Prop),
    ty <> xty ->
    (exists rhs, g ty xty = Some rhs /\ Q rhs) ->
    (exists rhs, (if tydesc_eq_dec A ty xty then f ty xty else g ty xty) = Some rhs /\ Q rhs).
intros.
destruct (tydesc_eq_dec _ _ _); [ exfalso; congruence | ].
auto.
Qed.


Lemma unpack_ty_helper1
    (DT : Set) (D : eval_bits DT) (DP : forall ty : tydesc D, Type) DR
        dden dty dden' (df : DP dty -> option DR) drhs
    (AT : Set) (A : eval_bits AT) (AP : forall ty : tydesc A, Type) AR
        aden aty aden' (af : AP aty -> option AR)
        (P : AR -> Prop) :
    unpack_ty (R := DR) D dty dden df = Some drhs ->
    dden = Some (existT DP dty dden') ->
    aden = Some (existT AP aty aden') ->
    (df dden' = Some drhs ->
        exists arhs, af aden' = Some arhs /\ P arhs) ->
    exists arhs, unpack_ty (R := AR) A aty aden af = Some arhs /\ P arhs.
intros0 Hunpack Hdden Haden Hinner.
subst dden aden. simpl in *.
destruct (tydesc_eq_dec _ dty dty); [ | exfalso; congruence ].
destruct (tydesc_eq_dec _ aty aty); [ | exfalso; congruence ].
fix_eq_rect; eauto using tydesc_eq_dec.
Qed.

Lemma unpack_ty_some_ex
    (T : Set) (A : eval_bits T) (P : forall ty : tydesc A, Type) R
        den ty den' (f : P ty -> option R)
        (Q : R -> Prop) :
    den = Some (existT P ty den') ->
    (exists rhs, f den' = Some rhs /\ Q rhs) ->
    (exists rhs, unpack_ty (R := R) A ty den f = Some rhs /\ Q rhs).
intros0 Hden Hinner.
subst den. simpl in *.
destruct (tydesc_eq_dec _ ty ty); [ | exfalso; congruence ].
fix_eq_rect; eauto using tydesc_eq_dec.
Qed.

Lemma unpack_ty_some_inv : forall
    (T : Set) (D : eval_bits T) (P : forall ty : tydesc D, Type) R
        xty den f rhs
        (Q : Prop),
    (forall val,
        den = Some (existT P xty val) ->
        f val = Some rhs ->
        Q) ->
    unpack_ty (R := R) D xty den f = Some rhs -> Q.
intros0 HQ Hunpack.
destruct den as [ s | ]; try discriminate.
destruct s. simpl in Hunpack.
destruct (tydesc_eq_dec _ _ _); try discriminate.
subst xty. fix_eq_rect; eauto using tydesc_eq_dec.
Qed.



Lemma denote'_refine : forall e dden,
    denote' D e = Some dden ->
    exists aden,
        denote' A e = Some aden /\
        refine_state_fn' dden aden.
induction e using expr_rect_mut with
    (Pl := fun es => forall ddens,
        denote'_list D es = Some ddens ->
        exists adens,
            denote'_list A es = Some adens /\
            refine_state_fn_list' ddens adens);
[ .. | eauto | eauto ];
intros0 Hden.

Local Opaque multi.
Local Opaque multi_get.
Local Opaque multi_set.
Local Opaque A.
Local Opaque D.

all: simpl in *; unfold pack_denot in *; inject_some.
all: try (eexists; split; [reflexivity|]; unfold refine_state_fn', lift).

- constructor.  { constructor. }
  intros. inject_pair.
  split; [|split]; auto.
  + eapply MForall2_get. assumption.

- constructor.  { constructor. }
  intros. inject_pair.
  split; [|split]; auto.
  + eapply MForall2_get. assumption.

- constructor.  { constructor. }
  intros. inject_pair.
  split; [|split]; auto.
  + eapply convert_lit_refine.

- (* Unary *)
  handle_unpack_opt.
  handle_unpack_opt.
    { on >refine_state_fn, invc. eapply unop_denote_refine; eauto. }
    simpl in *.

  eexists. split; [reflexivity|]. inject_some. simpl.

  constructor.  { on >refine_unop, invc. auto. }
  intros.  clear IHe.

  on >refine_state_fn, invc.  specialize_refinement.
    repeat find_rewrite. inject_pair.
  on >refine_unop, invc.  specialize_refinement.

  eauto.

- (* Binary *)
  handle_unpack_opt.
  handle_unpack_opt.
  handle_unpack_opt.
    { inv Hrefine. inv Hrefine0. eapply binop_denote_refine; eauto. }
    simpl in *.

  eexists. split; [reflexivity|]. inject_some. simpl.

  constructor.  { on >refine_binop, invc. auto. }
  intros.  clear IHe1 IHe2.

  on >(refine_state_fn dty), invc.  specialize_refinement.
    repeat find_rewrite. inject_pair.
  on >(refine_state_fn dty0), invc.  specialize_refinement.
    repeat find_rewrite. inject_pair.
  on >refine_binop, invc.  specialize_refinement.

  eauto.

- (* Varary *)
  fold (denote'_list D xs) in *.
  fold (denote'_list A xs) in *.
  handle_unpack_opt.
  handle_unpack_opt.
    { inv Hrefine. eapply varop_denote_refine; eauto. }
    simpl in *.

  eexists. split; [reflexivity|]. inject_some. simpl.

  constructor.  { on >refine_varop, invc. auto. }
  intros.  clear IHe.

  on >refine_state_fn_list, invc.  specialize_refinement.
    repeat find_rewrite. inject_pair.
  on >refine_varop, invc.  specialize_refinement.

  eauto.

- (* Assign *)

  (* TODO - put unpack_ty stuff into the handle_unpack_opt tactic *)
  on _, invc_using unpack_ty_some_inv.
    destruct (IHe _ **) as ([? ?] & HH & ?). simpl in *.
    on >refine_state_fn, invc.
    assert (x = var_ty A) by eauto using ty_rel_inj, var_ty_rel. subst x.
    eapply unpack_ty_some_ex; eauto.  clear HH.

  eexists. split; [reflexivity|]. inject_some. simpl.

  constructor.  { eauto using nil_ty_rel. }
  intros.  clear IHe.

  specialize_refinement.
    repeat find_rewrite. inject_pair.

  split; [|split]; eauto using set_MForall2.
  + econstructor.

- (* XAssign *)

  on _, invc_using unpack_ty_some_inv.
    destruct (IHe _ **) as ([? ?] & HH & ?). simpl in *.
    on >refine_state_fn, invc.
    assert (x = xvar_ty A) by eauto using ty_rel_inj, xvar_ty_rel. subst x.
    eapply unpack_ty_some_ex; eauto.  clear HH.

  eexists. split; [reflexivity|]. inject_some. simpl.

  constructor.  { eauto using nil_ty_rel. }
  intros.  clear IHe.

  specialize_refinement.
    repeat find_rewrite. inject_pair.

  split; [|split]; eauto using set_MForall2.
  + econstructor.

- (* Cond *)
  handle_unpack_opt.
  handle_unpack_opt.
  handle_unpack_opt.
  handle_unpack_opt.
    { do 3 on >refine_state_fn, invc. eapply ternop_denote_refine; eauto. }
    simpl in *.

  eexists. split; [reflexivity|]. inject_some. simpl.

  constructor.  { on >refine_ternop, invc. auto. }
  intros.  clear IHe1 IHe2 IHe3.

  on >(refine_state_fn dty), invc.  specialize_refinement.
    repeat find_rewrite. inject_pair.
  on >(refine_state_fn dty0), invc.  specialize_refinement.
    repeat find_rewrite. inject_pair.
  on >(refine_state_fn dty1), invc.  specialize_refinement.
    repeat find_rewrite. inject_pair.
  on >refine_ternop, invc.  specialize_refinement.

  eauto.

- (* Seq *)
  handle_unpack_opt.
  handle_unpack_opt.
  destruct (tydesc_eq_dec D _ _); [ | destruct (tydesc_eq_dec D _ _); [ | discriminate Hden ] ].

  + assert (aty = nil_ty A). { eapply nil_rel_fwd. invc Hrefine. auto. }
    subst aty. destruct (tydesc_eq_dec A _ _); [ | exfalso; congruence ].
    eexists. split; [ reflexivity | ]. inject_some. simpl.
    constructor. { invc Hrefine0. auto. } intros.

    on >(refine_state_fn (nil_ty D)), invc.  specialize_refinement.
      repeat find_rewrite. inject_pair.
    on >(refine_state_fn dty0), invc.  specialize_refinement.
      repeat find_rewrite. inject_pair.
    auto.

  + assert (aty <> nil_ty A).
      { on (dty <> _), contradict. eapply nil_rel_rev. invc Hrefine. auto. }
    destruct (tydesc_eq_dec A _ _); [ exfalso; congruence | ].
    assert (aty0 = nil_ty A). { eapply nil_rel_fwd. invc Hrefine0. auto. }
    subst aty0. destruct (tydesc_eq_dec A _ _); [ | exfalso; congruence ].
    eexists. split; [ reflexivity | ]. inject_some. simpl.
    constructor. { invc Hrefine. auto. } intros.

    on >(refine_state_fn dty), invc.  specialize_refinement.
      repeat find_rewrite. inject_pair.
    on >(refine_state_fn (nil_ty D)), invc.  specialize_refinement.
      repeat find_rewrite. inject_pair.
    auto.

- (* nil *) discriminate.

- destruct es as [| e' es ].

  + (* singleton list *)
    handle_unpack_opt.

    eexists. split; [reflexivity|]. inject_some. simpl.

    constructor.  { on >refine_state_fn, invc. auto. }
    intros.  clear IHe IHe0.

    on >(refine_state_fn dty), invc.  specialize_refinement.
      repeat find_rewrite. inject_pair.
    auto.

  + (* singleton list *)
    remember (e' :: es) as e'_es.
    handle_unpack_opt.
    handle_unpack_opt.
    destruct (tydesc_eq_dec _ _ _); try discriminate.
      subst dty0.

    destruct (tydesc_eq_dec _ _ _); cycle 1.
      { on (aty <> _), contradict.
        invc Hrefine. invc Hrefine0.
        eapply ty_rel_inj; eauto. }
      subst aty0.

    eexists. split; [reflexivity|]. inject_some. simpl.

    constructor.  { on >refine_state_fn, invc. auto. }
    intros.  clear IHe IHe0.

    on >(refine_state_fn dty), invc.  specialize_refinement.
      repeat find_rewrite. inject_pair.
    on >(refine_state_fn_list dty), invc.  specialize_refinement.
      repeat find_rewrite. inject_pair.
    auto.

Qed.

Local Transparent A.
Local Transparent D.

Lemma denote_refine : forall e dden,
    Dbl.denote e = Some dden ->
    exists aden,
        Abs.denote e = Some aden /\
        refine_state_fn_noxvar Dbl.Dbl Abs.Abs dden aden.
intros. unfold Dbl.denote in *.

on _, invc_using unpack_ty_some_inv.
forward eapply denote'_refine as HH; eauto.  destruct HH as (aden & Haden & Hrefine).
  simpl in Hrefine. destruct aden as [aty aden].
  change e_double with (ty_denote D Dbl.Dbl) in val.
  assert (aty = Abs.Abs).  { inv Hrefine. on >ty_rel, invc. auto. }  subst aty.
unfold Abs.denote.
eapply unpack_ty_some_ex; eauto.

eexists. split; [ reflexivity | ]. inject_some.
constructor. { invc Hrefine. auto. }  intros.
change (tt, tt, tt, tt, tt, tt, tt, tt, tt, tt, tt, tt) with (multi_rep 12 tt) in *.

assert (MForall2 (refine_value (xvar_ty D) (xvar_ty A)) (multi_rep 12 tt) (multi_rep 12 tt)).
  { eapply rep_MForall2. constructor. }

on >refine_state_fn, invc.  specialize_refinement.
  repeat find_rewrite. inject_pair.
auto.
Qed.


Lemma refine_state_fn_noxvar_dbl_abs_inv : forall df af,
    refine_state_fn_noxvar Dbl.Dbl Abs.Abs df af ->
    (forall dsv asv dsv' dr asv' ar,
        MForall2 (refine_value _ _) dsv asv ->
        df dsv = (dsv', dr) ->
        af asv = (asv', ar) ->
        MForall2 (refine_value _ _) dsv' asv' /\
        refine_value _ _ dr ar).
inversion 1. auto.
Qed.

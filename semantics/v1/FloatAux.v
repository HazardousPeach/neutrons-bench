Require Import Reals.
Require Import Flocq.Appli.Fappli_IEEE.
Require Import Flocq.Appli.Fappli_IEEE_bits.
Require Import Flocq.Core.Fcore.

Require Import NArith.
Require Import ZArith.

Require Import v1.NeutronTactics.

Set Default Timeout 10.
Set Implicit Arguments.

Local Open Scope Z.

Definition Ns2Z (n : N) (s : bool) : Z :=
    match n with
    | N0 => Z0
    | Npos p => if s then Zneg p else Zpos p
    end.

Definition FF2Z_trunc_aux s m e : Z :=
    let n := match e with
        | Z0 => N.pos m
        | Zpos p => N.shiftl (N.pos m) (N.pos p)
        | Zneg p => N.shiftr (N.pos m) (N.pos p)
        end in
    Ns2Z n s.

Definition FF2Z_trunc (f : full_float) : Z :=
    match f with
    | F754_zero _ => 0
    | F754_infinity _ => 0
    | F754_nan _ _ => 0
    | F754_finite s m e => FF2Z_trunc_aux s m e
    end.

Definition FF2Z_safe_aux s m e : option Z :=
    let n := match e with
        | Z0 => Some (N.pos m)
        | Zpos p => Some (N.shiftl (N.pos m) (N.pos p))
        | Zneg p =>
                if N.eqb (N.land (N.pos m) (N.ones (N.pos p))) 0
                    then Some (N.shiftr (N.pos m) (N.pos p))
                    else None
        end in
    match n with
    | Some n => Some (Ns2Z n s)
    | None => None
    end.

Definition FF2Z_safe (f : full_float) : option Z :=
    match f with
    | F754_zero _ => Some 0%Z
    | F754_infinity _ => None
    | F754_nan _ _ => None
    | F754_finite s m e => FF2Z_safe_aux s m e
    end.

Lemma FF2Z_safe_trunc_aux_match : forall s m e z,
    FF2Z_safe_aux s m e = Some z ->
    FF2Z_trunc_aux s m e = z.
intros until 0.
destruct e; unfold FF2Z_safe_aux, FF2Z_trunc_aux;
try (injection 1; eauto).

destruct (N.eqb _ _) eqn:?.
- injection 1. eauto.
- discriminate 1.
Qed.

Lemma FF2Z_safe_trunc_match : forall f z,
    FF2Z_safe f = Some z ->
    FF2Z_trunc f = z.
intros ? ?. destruct f; simpl; [ destruct b | | | ];
try solve [ injection 1; eauto | discriminate 1 ].
apply FF2Z_safe_trunc_aux_match.
Qed.


Definition Z2FF (z : Z) : full_float :=
    match z with
    | Z0 => F754_zero false
    | Zpos p => F754_finite false p 0
    | Zneg p => F754_finite true p 0
    end.

Lemma Z2FF_FF2Z_safe : forall z, FF2Z_safe (Z2FF z) = Some z.
intros.
destruct z; simpl.
- reflexivity.
- unfold FF2Z_safe_aux. simpl. reflexivity.
- unfold FF2Z_safe_aux. simpl. reflexivity.
Qed.

Definition N2R n :=
    match n with
    | N0 => 0%R
    | Npos p => P2R p
    end.

Definition lift_pos_z (f : positive -> positive) : Z -> Z :=
    fun z =>
    match z with
    | Z0 => Z0
    | Zpos p => Zpos (f p)
    | Zneg p => Zneg (f p)
    end.

Lemma pos_iter_z : forall f a n,
    Z.pos (Pos.iter f a n) =
    Pos.iter (lift_pos_z f) (Z.pos a) n.
first_induction n; intros; simpl;
repeat rewrite <- IHn; reflexivity.
Qed.

Lemma pos_iter_fext : forall A (f f' : A -> A) a n,
    (forall x, f x = f' x) ->
    Pos.iter f a n = Pos.iter f' a n.
first_induction n; intros0 Hfext; simpl.
- rewrite Hfext. f_equal.
  erewrite IHn; eauto. f_equal.
  eauto.
- erewrite IHn; eauto. f_equal.
  eauto.
- eauto.
Qed.

Lemma z_pos_shiftl : forall a n,
    Z.pos (Pos.shiftl a (N.pos n)) = Z.shiftl (Z.pos a) (Z.pos n).
intros. simpl.
rewrite pos_iter_z. eapply pos_iter_fext.
intros. destruct x; simpl; reflexivity.
Qed.

Lemma N2Z_inj_pos_iter : forall f f' a n,
    (forall n, Z.of_N (f n) = f' (Z.of_N n)) ->
    Z.of_N (Pos.iter f a n) = Pos.iter f' (Z.of_N a) n.
first_induction n; intros0 Hinj; simpl.

- erewrite Hinj. f_equal.
  erewrite IHn; eauto. f_equal.
  eauto.
- erewrite IHn; eauto. f_equal.
  eauto.
- eauto.
Qed.

Lemma nshiftr_zshiftr_pos : forall a n,
    Z.of_N (N.shiftr (N.pos a) (N.pos n)) = Z.shiftr (Z.pos a) (Z.pos n).
first_induction n; intros;
unfold Z.shiftr, Z.shiftl; simpl.

- rewrite N2Z.inj_div2. f_equal.
  rewrite N2Z_inj_pos_iter with (f' := Z.div2); eauto using N2Z.inj_div2. f_equal.
  rewrite N2Z_inj_pos_iter with (f' := Z.div2); eauto using N2Z.inj_div2.

- rewrite N2Z_inj_pos_iter with (f' := Z.div2); eauto using N2Z.inj_div2. f_equal.
  rewrite N2Z_inj_pos_iter with (f' := Z.div2); eauto using N2Z.inj_div2.

- destruct a; reflexivity.
Qed.

Lemma div2_N2R : forall n,
    N.even n = true ->
    N2R (N.div2 n) = (N2R n * / 2)%R.
induction n; intros0 Heven; simpl.
{ ring. }

assert (2 <> 0)%R by (eapply tech_Rplus; eauto with real).

destruct p; try discriminate Heven.
replace (p~0)%positive with (2 * p)%positive by reflexivity.
unfold N2R. repeat rewrite P2R_INR.
rewrite Pos2Nat.inj_mul.  rewrite mult_INR.
simpl. field.
Qed.

Lemma div2_IZR : forall z,
    z >= 0 ->
    Z.even z = true ->
    IZR (Z.div2 z) = (IZR z * / 2)%R.
intros0 Hge Heven.
destruct z.

- (* z = 0 *)
  simpl. field.

- (* z > 0 *)
  replace (IZR (Z.pos p)) with (N2R (N.pos p)) by (rewrite <- Z2R_IZR; reflexivity).
  rewrite <- div2_N2R; cycle 1.
  { destruct p; simpl in *; congruence. }
  destruct p; simpl; try rewrite P2R_INR; reflexivity.

- (* z < 0 *)
  exfalso. compute in Hge. eauto.
Qed.

Lemma N_succ_add : forall n, N.succ n = (1 + n)%N.
destruct n; simpl; try reflexivity. f_equal.
fold (1 + p)%positive. eauto using Pplus_one_succ_l.
Qed.

Lemma N_ones_succ_double : forall n,
    N.ones (1 + n) = N.succ_double (N.ones n).
intros.
rewrite N.ones_add. simpl.
unfold N.ones at 2. simpl.
rewrite N.add_comm.
unfold N.succ_double.
destruct (N.ones n); simpl; reflexivity.
Qed.

Lemma N_ones_div2 : forall n,
    N.div2 (N.ones (1 + n)) = N.ones n.
intros.
rewrite N_ones_succ_double.
rewrite N.div2_succ_double.
reflexivity.
Qed.

Lemma N_even_testbit : forall n, N.even n = true <-> N.testbit n 0 = false.
intros.
destruct n; simpl.
{ constructor; reflexivity. }
destruct p; simpl; firstorder congruence.
Qed.

Lemma mult_N2R : forall n m, (N2R (n * m) = N2R n * N2R m)%R.
intros.
destruct n; destruct m; simpl; eauto with real.
repeat rewrite P2R_INR.
rewrite Pos2Nat.inj_mul.  rewrite mult_INR.
reflexivity.
Qed.

Lemma nshiftr_pos_eq_z : forall a n p,
    N.shiftr (N.pos a) (N.pos n) = N.pos p ->
    Z.shiftr (Z.pos a) (Z.pos n) = Z.pos p.
intros. rewrite <- nshiftr_zshiftr_pos. rewrite H. reflexivity.
Qed.

Lemma shiftr_N2R : forall n a,
    N.land a (N.ones n) = 0%N ->
    N2R (N.shiftr a n) = (N2R a * / N2R (N.pow 2 n))%R.
induction n using N.peano_ind; intros0 Hones.
{ simpl. field. }

replace (N.succ n) with (1 + n)%N by (eauto using N_succ_add).
rewrite <- N.shiftr_shiftr.
rewrite IHn; cycle 1.
{ replace (N.ones n) with (N.shiftr (N.ones (N.succ n)) 1); cycle 1.
  { simpl. replace (N.succ n) with (1 + n)%N by (eauto using N_succ_add).
    eapply N_ones_div2. }
  rewrite <- N.shiftr_land. rewrite Hones. simpl. reflexivity. }
unfold N.shiftr, Pos.iter.
rewrite div2_N2R; cycle 1.
{ assert (Hbits : N.testbit (N.land a (N.ones (N.succ n))) 0%N = N.testbit a 0%N).
  { rewrite N.land_spec. rewrite N.ones_spec_low; cycle 1.
    { unfold N.succ. destruct n; compute; congruence. }
    rewrite Bool.andb_true_r. reflexivity. }
  rewrite Hones in Hbits. simpl in Hbits.
  rewrite N_even_testbit. congruence. }
rewrite <- N_succ_add. rewrite N.pow_succ_r; cycle 1.
{ destruct n; compute; congruence. }
rewrite mult_N2R. simpl.
field.
assert (2^n <> 0)%N by (eapply N.pow_nonzero; discriminate).
destruct (2^n)%N; try congruence.
simpl. rewrite P2R_INR. eapply not_0_INR.
assert (0 < Pos.to_nat p)%nat by (eauto using Pos2Nat.is_pos).
omega.
Qed.

Lemma N2R_IZR_of_N : forall n, IZR (Z.of_N n) = N2R n.
intros. simpl.
destruct n; simpl; try reflexivity.
rewrite P2R_INR. reflexivity.
Qed.

Lemma shiftr_IZR_pos : forall n a,
    N.land (N.pos a) (N.ones (N.pos n)) = 0%N ->
    IZR (Z.shiftr (Z.pos a) (Z.pos n)) = (IZR (Z.pos a) * / IZR (Z.pow_pos 2 n))%R.
intros0 Hand.
rewrite <- nshiftr_zshiftr_pos.
rewrite N2R_IZR_of_N. rewrite shiftr_N2R; eauto.
repeat rewrite <- N2R_IZR_of_N. 
rewrite N2Z.inj_pow.
rewrite Z.pow_pos_fold.
simpl. reflexivity.
Qed.

Lemma FF2Z_safe_Z2FF : forall ff z,
    FF2Z_safe ff = Some z ->
    FF2R radix2 ff = FF2R radix2 (Z2FF z).
intros0 Hsafe.
destruct ff as [ s | s | s n | s m e ]; unfold FF2Z_safe in Hsafe; try congruence.

- (* zero *)
  inversion Hsafe. subst.
  simpl. reflexivity.

- (* finite *)
  unfold FF2Z_safe_aux in Hsafe.
  destruct e.

  + (* e = 0 *)
    inversion Hsafe. subst.
    destruct s; simpl; reflexivity.

  + (* e > 0 *)
    match type of Hsafe with Some ?x = Some ?y =>
            assert (x = y) by congruence end.  subst.
    unfold Ns2Z, Z2FF.
    destruct (N.shiftl _ _) eqn:?.
    { simpl in *. congruence. }
    unfold N.shiftl in *.
    match goal with | [ H : N.pos ?x = N.pos ?y |- _ ] =>
            assert (x = y) by congruence end. subst.

    destruct s;
    simpl; unfold Fcore_defs.F2R; simpl;
    repeat match goal with
    | [ |- context [ P2R ?p ] ] => replace (P2R p) with (Z2R (Z.pos p)) by reflexivity
    end;
    fold (Pos.shiftl m (N.pos p));
    rewrite z_pos_shiftl;
    (rewrite Z.shiftl_mul_pow2; [ | discriminate 1 ]);
    rewrite Z2R_mult;
    simpl; ring.

  + (* e < 0 *)
    break_match; break_if; try congruence.
    rewrite N.eqb_eq in *.
    repeat match goal with
    | [ H : Some ?x = Some ?y |- _ ] =>
            let H' := fresh "H" in
            rename H into H';
            assert (H : x = y) by congruence;
            clear H'
    end.
    subst z.
    unfold Ns2Z, Z2FF.

    destruct n.
    { (* Contradictory case: `N.pos m = 0%N`. *)
      erewrite N.shiftr_eq_0_iff in *.
      match goal with
      | [ H : _ \/ _ |- _ ] => destruct H
      end; [ congruence | ].
      match goal with
      | [ H : _ /\ _ |- _ ] => destruct H as [ Hl Hr ]
      end.
      eapply N.land_ones_low in Hr.
      congruence. }

    destruct s;
    simpl; unfold F2R; simpl;
    repeat match goal with
    | [ |- context [ P2R ?p ] ] => replace (P2R p) with (Z2R (Z.pos p)) by reflexivity
    end.

    -- eapply nshiftr_pos_eq_z in Heqo.
       rewrite <- Heqo.
       repeat rewrite Z2R_IZR.
       rewrite shiftr_IZR_pos; eauto. ring.

    -- eapply nshiftr_pos_eq_z in Heqo.
       rewrite <- Heqo.
       repeat rewrite Z2R_IZR.
       rewrite shiftr_IZR_pos; eauto. ring.
Qed.


Section binary_float.
Variable prec : Z.
Variable emax : Z.

Variable Hprec : (0 < prec).
Variable Hprec_emax : (prec < emax).

Definition whole r := IZR (up r) = (r + 1)%R.

Open Scope R.

Lemma whole_ex : forall r, whole r -> exists z, r = IZR z.
intros0 Hr.
exists (up r - 1)%Z.
eapply (Rplus_eq_reg_r 1). rewrite <- Hr.
rewrite minus_IZR. simpl. ring.
Qed.

Lemma up_range : forall r, r < IZR (up r) <= r + 1.
intros.
forward eapply (archimed r) as [ Hmin Hmax ].
split.
- eauto using Rlt_gt.
- eapply (Rplus_le_compat_r r) in Hmax.
  unfold Rminus in Hmax.
  rewrite Rplus_assoc in Hmax. replace (- r + r) with 0 in Hmax by ring.
  rewrite Rplus_0_r in Hmax.
  rewrite Rplus_comm in Hmax.
  assumption.
Qed.

Lemma IZR_whole : forall z, whole (IZR z).
intros. unfold whole.
forward eapply (up_range (IZR z)) as [ Hmin Hmax ].
replace 1 with (IZR 1) in * by reflexivity.
rewrite <- plus_IZR in *.
f_equal. eapply lt_IZR in Hmin. eapply le_IZR in Hmax.
omega.
Qed.
Hint Resolve IZR_whole.

Lemma up_IZR : forall z, up (IZR z) = (z + 1)%Z.
intros. forward eapply (IZR_whole z) as Hz. unfold whole in Hz.
replace 1 with (IZR 1) in Hz by reflexivity. rewrite <- plus_IZR in Hz.
eapply eq_IZR in Hz. assumption.
Qed.

Lemma plus_whole : forall r1 r2, whole r1 -> whole r2 -> whole (r1 + r2).
intros0 Hr1 Hr2.
eapply whole_ex in Hr1. destruct Hr1 as [z1 Hz1].
eapply whole_ex in Hr2. destruct Hr2 as [z2 Hz2].
subst. unfold whole.
replace 1 with (IZR 1) by reflexivity.
repeat rewrite <- plus_IZR.
rewrite up_IZR. reflexivity.
Qed.
Hint Resolve plus_whole.

Lemma mult_whole : forall r1 r2, whole r1 -> whole r2 -> whole (r1 * r2).
intros0 Hr1 Hr2.
eapply whole_ex in Hr1. destruct Hr1 as [z1 Hz1].
eapply whole_ex in Hr2. destruct Hr2 as [z2 Hz2].
subst. unfold whole.
replace 1 with (IZR 1) by reflexivity.
repeat rewrite <- mult_IZR.
repeat rewrite <- plus_IZR. 
rewrite up_IZR. reflexivity.
Qed.
Hint Resolve mult_whole.

Lemma pow_whole : forall r1 n2, whole r1 -> whole (r1 ^ n2).
intros0 Hr1.
eapply whole_ex in Hr1. destruct Hr1 as [z1 Hz1].
subst. unfold whole.
replace 1 with (IZR 1) by reflexivity.
repeat rewrite pow_IZR.
repeat rewrite <- plus_IZR. 
rewrite up_IZR. reflexivity.
Qed.
Hint Resolve pow_whole.

Lemma opp_whole : forall r, whole r -> whole (-r).
intros0 Hr.
eapply whole_ex in Hr. destruct Hr as [z Hz].
subst. unfold whole.
replace 1 with (IZR 1) by reflexivity.
repeat rewrite <- opp_IZR.
repeat rewrite <- plus_IZR.
rewrite up_IZR. reflexivity.
Qed.
Hint Resolve opp_whole.

Lemma minus_whole : forall r1 r2, whole r1 -> whole r2 -> whole (r1 - r2).
intros0 Hr1 Hr2.
unfold Rminus.
eauto using plus_whole, opp_whole.
Qed.
Hint Resolve minus_whole.


Lemma binary_normalize_int_zero : forall mode zs,
    B2R _ _ (binary_normalize _ _ Hprec Hprec_emax mode 0 0 zs) =
    F2R (Float radix2 0 0).
intros.
destruct mode; compute; ring.
Qed.

Lemma whole_up_opp : forall r, whole r -> (up (-r) = -(up r) + 2)%Z.
intros0 Hr.
forward eapply (archimed (-r)) as [Hneg1 Hneg2].
forward eapply (archimed r) as [Hpos1 Hpos2].

assert (Htwo : (IZR (up (-r)) + IZR (up r) <= 2)).
{ forward eapply (Rplus_le_compat _ _ _ _ Hneg2 Hpos2) as HH.
  unfold Rminus in HH.
  rewrite Ropp_involutive in HH.
  rewrite Rplus_assoc in HH.
  replace (r + (IZR (up r) + -r)) with (IZR (up r)) in HH by ring.
  exact HH. }
assert (Hone : (IZR (up (-r)) + IZR (up r) > 1)).
{ rewrite Hr.
  replace 1 with (-r + (r + 1)) at 2 by ring.
  eapply Rplus_gt_compat_r. assumption. }

assert (up (-r) + up r > 1)%Z.
{ replace 1 with (IZR 1) in Hone by reflexivity.
  rewrite <- plus_IZR in Hone.
  eapply Rgt_lt in Hone.
  eapply lt_IZR in Hone.
  omega. }

assert (up (-r) + up r <= 2)%Z.
{ replace 2 with (IZR 2) in Htwo by reflexivity.
  rewrite <- plus_IZR in Htwo.
  eapply le_IZR in Htwo.
  omega. }

omega.
Qed.

Lemma whole_Zfloor : forall r, whole r -> IZR (Zfloor r) = r.
intros0 Hint.
unfold Zfloor.
rewrite minus_IZR. rewrite Hint. simpl. ring.
Qed.
Hint Resolve whole_Zfloor.

Lemma whole_Zceil : forall r, whole r -> IZR (Zceil r) = r.
intros0 Hint.
unfold Zceil, Zfloor.
rewrite whole_up_opp; eauto.
replace (- (- up r + 2 - 1))%Z with (up r - 1)%Z by omega.
rewrite minus_IZR. rewrite Hint. simpl. ring.
Qed.
Hint Resolve whole_Zceil.

Lemma whole_Ztrunc : forall r, whole r -> IZR (Ztrunc r) = r.
intros0 Hint.
unfold Ztrunc. break_if.
- eauto using whole_Zceil.
- eauto using whole_Zfloor.
Qed.
Hint Resolve whole_Ztrunc.

Lemma whole_Znearest : forall r f, whole r -> IZR (Znearest f r) = r.
intros0 Hint.
unfold Znearest. break_match; try break_if; eauto using whole_Zceil, whole_Zfloor.
Qed.
Hint Resolve whole_Znearest.

Lemma whole_round_mode : forall r m, whole r -> IZR (round_mode m r) = r.
intros0 Hint.
destruct m; simpl;
eauto using whole_Zceil, whole_Zfloor, whole_Ztrunc, whole_Znearest.
Qed.
Hint Resolve whole_round_mode.


Lemma whole_scaled_mantissa : forall z,
    (0 < Z.abs z < 2 ^ (prec - 1))%Z ->
    whole (scaled_mantissa radix2 (FLT_exp (3 - emax - prec) prec) (Z2R z)).
pose proof Hprec as Hprec.
pose proof Hprec_emax as Hprec_emax.

intros0 Hrange. unfold scaled_mantissa.
destruct (canonic_exp _ _ _) eqn:Hcexp; simpl.

- (* cexp = 0 *)
  replace 1 with (IZR 1) by reflexivity. rewrite Z2R_IZR. eauto.

- (* cexp > 0 *)
  remember (canonic_exp _ _ _) as cexp eqn:Hcexp'.
  cut (cexp < 0)%Z.
  { intro Hlt. assert (Z.pos p > 0)%Z by (eapply Zgt_pos_0). omega. }
  rewrite Hcexp'. clear Hcexp Hcexp'.

  unfold canonic_exp, FLT_exp.

  assert (Hmin : (0 < ln_beta_val _ _ (ln_beta radix2 (Z2R z)))%Z).
  { eapply ln_beta_gt_Zpower.
    - destruct z; unfold Z.abs in *; try omega.
      forward eapply (Zlt_neg_0 p0). omega.
    - simpl. omega. }
  rewrite Z.max_l by omega.

  assert (Hmax : (ln_beta_val _ _ (ln_beta radix2 (Z2R z)) <= prec - 1)%Z).
  { eapply ln_beta_le_Zpower.
    - destruct z; unfold Z.abs in *; try omega.
      forward eapply (Zlt_neg_0 p0). omega.
    - unfold radix2, radix_val. omega. }
  omega.

- (* cexp < 0 *)
  repeat rewrite Z2R_IZR. eauto.
Qed.

Lemma no_overflow_int : forall z mode,
    (-(2 ^ (prec - 1)) < z < 2 ^ (prec - 1))%Z ->
    Rabs (round  radix2  (FLT_exp  (3  -  emax  -  prec)  prec)  (round_mode mode) (Z2R z)) <
    (bpow  radix2  emax).
pose proof Hprec as Hprec_.
pose proof Hprec_emax as Hprec_emax_.

intros0 Hrange.

remember (bpow _ _) as large_number. unfold round, F2R. simpl.

rewrite Z2R_IZR, whole_round_mode; cycle 1.
{ destruct z.
  - unfold scaled_mantissa. simpl. rewrite Rmult_0_l.
    replace 0 with (IZR 0) by reflexivity. eapply IZR_whole.
  - eapply whole_scaled_mantissa; eauto.
    unfold Z.abs. forward eapply (Zgt_pos_0 p). omega.
  - eapply whole_scaled_mantissa; eauto.
    replace (Z.neg p) with (-Z.pos p)%Z in * by reflexivity.
    unfold Z.opp, Z.abs. forward eapply (Zgt_pos_0 p). omega. }

unfold scaled_mantissa. remember (canonic_exp _ _ _) as cexp.
repeat rewrite Rmult_assoc.
rewrite <- bpow_plus. replace (- cexp + cexp)%Z with 0%Z by omega.
simpl. rewrite Rmult_1_r.

subst large_number.
rewrite <- Z2R_Zpower; try omega.
repeat rewrite Z2R_IZR. rewrite <- abs_IZR. eapply IZR_lt.

unfold radix2, radix_val.
assert (Z.abs z < 2 ^ (prec - 1))%Z.
{ destruct z; unfold Z.abs.
  - eapply Z.pow_pos_nonneg; omega.
  - omega.
  - replace (Z.neg p) with (-Z.pos p)%Z in * by reflexivity. omega. }
assert (2 ^ (prec - 1) < 2 ^ emax)%Z.
{ eapply Z.pow_lt_mono_r; omega. }
omega.
Qed.

Lemma no_overflow_int_bool : forall z mode,
    (-(2 ^ (prec - 1)) < z < 2 ^ (prec - 1))%Z ->
    Rlt_bool
        (Rabs (round  radix2  (FLT_exp  (3  -  emax  -  prec)  prec)  (round_mode  mode) (Z2R z)))
        (bpow  radix2  emax) = true.
intros0 Hrange.
unfold Rlt_bool. rewrite Rcompare_Lt. { reflexivity. }
eapply no_overflow_int. assumption.
Qed.

Lemma no_overflow_int_bool' : forall r z mode,
    r = Z2R z ->
    (-(2 ^ (prec - 1)) < z < 2 ^ (prec - 1))%Z ->
    Rlt_bool
        (Rabs (round  radix2  (FLT_exp  (3  -  emax  -  prec)  prec)  (round_mode  mode) r))
        (bpow  radix2  emax) = true.
intros. subst. eapply no_overflow_int_bool. assumption.
Qed.

Lemma binary_normalize_int_pos : forall mode m e zs,
    (0 < m < 2 ^ (prec - 1))%Z ->
    (e = 0)%Z ->
    B2R _ _ (binary_normalize _ _ Hprec Hprec_emax mode m e zs) =
    F2R (Float radix2 m e).
pose proof Hprec as Hprec_.
pose proof Hprec_emax as Hprec_emax_.

intros.
forward refine (binary_normalize_correct prec emax Hprec Hprec_emax mode m e zs) as HH.
rewrite no_overflow_int_bool' with (z := m) in HH; cycle 1.
{ unfold F2R. subst e. simpl.  ring. }
{ omega. }

destruct HH as ( HB2R & Hfin & Hsign ).
rewrite HB2R.
unfold round.

unfold F2R; simpl.
repeat rewrite Z2R_IZR. rewrite whole_round_mode.
- unfold scaled_mantissa. remember (canonic_exp _ _ _) as cexp.
  replace (bpow radix2 e) with (bpow radix2 e * 1) by ring.
  repeat rewrite Rmult_assoc. f_equal. f_equal.
  destruct cexp; simpl; field.
  + cut (Z.pow_pos 2 p <> 0)%Z.
    { intros. intro HH.
      replace 0 with (IZR 0) in HH by reflexivity.
      rewrite Z2R_IZR in HH. eapply eq_IZR in HH. eauto. }
    rewrite Z.pow_pos_fold.
    eapply Z.pow_nonzero; [ omega | ].
    compute. discriminate.
  + cut (Z.pow_pos 2 p <> 0)%Z.
    { intros. intro HH.
      replace 0 with (IZR 0) in HH by reflexivity.
      rewrite Z2R_IZR in HH. eapply eq_IZR in HH. eauto. }
    rewrite Z.pow_pos_fold.
    eapply Z.pow_nonzero; [ omega | ].
    compute. discriminate.
- subst e. simpl. rewrite Rmult_1_r. rewrite <- Z2R_IZR.
  eapply whole_scaled_mantissa; eauto.
  rewrite Z.abs_eq; omega.
Qed.

Lemma binary_normalize_int_neg : forall mode m e zs,
    (-(2 ^ (prec - 1)) < m < 0)%Z ->
    (e = 0)%Z ->
    B2R _ _ (binary_normalize _ _ Hprec Hprec_emax mode m e zs) =
    F2R (Float radix2 m e).
pose proof Hprec as Hprec_.
pose proof Hprec_emax as Hprec_emax_.

intros.

forward refine (binary_normalize_correct prec emax Hprec Hprec_emax mode m e zs) as Hpos.
rewrite no_overflow_int_bool' with (z := m) in Hpos; cycle 1.
{ unfold F2R. subst e. simpl.  ring. }
{ omega. }
remember (round _ _ _ _) as r_pos in Hpos.

forward refine (binary_normalize_correct prec emax Hprec Hprec_emax mode (-m) e (negb zs)) as Hneg.
rewrite no_overflow_int_bool' with (z := (-m)%Z) in Hneg; cycle 1.
{ unfold F2R. subst e. simpl. ring. }
{ omega. }
remember (round _ _ _ _) as r_neg in Hneg.

assert (Hsign : r_pos = - r_neg).
{ clear Hpos Hneg. subst r_pos r_neg.
  unfold round, F2R. simpl. repeat rewrite Z2R_IZR.

  rewrite whole_round_mode; cycle 1.
  { subst e. simpl. rewrite Rmult_1_r. rewrite <- Z2R_IZR.
    eapply whole_scaled_mantissa; eauto.
    rewrite Z.abs_neq; omega. }

  rewrite whole_round_mode; cycle 1.
  { subst e. simpl. rewrite Rmult_1_r. rewrite <- Z2R_IZR.
    eapply whole_scaled_mantissa; eauto.
    rewrite Z.abs_eq; omega. }

  unfold scaled_mantissa.
  remember (canonic_exp _ _ _) as cexp1 in |-*.
  remember (canonic_exp _ _ _) as cexp2 in |-*.
  repeat rewrite Rmult_assoc.
  repeat rewrite <- bpow_plus.
  replace (e + (- cexp1 + cexp1))%Z with e by omega.
  replace (e + (- cexp2 + cexp2))%Z with e by omega.
  rewrite opp_IZR.
  ring.
}

replace r_neg with (- r_pos) in Hneg by (rewrite Hsign; ring).

destruct Hpos as ( HB2R_pos & Hfin_pos & Hsign_pos ).
destruct Hneg as ( HB2R_neg & Hfin_neg & Hsign_neg ).
rewrite HB2R_pos.
rewrite <- Ropp_involutive at 1.
rewrite <- Ropp_involutive.
apply Ropp_eq_compat.
rewrite <- HB2R_neg.
rewrite binary_normalize_int_pos; try omega.
unfold F2R; simpl. repeat rewrite Z2R_IZR. rewrite opp_IZR. ring.
Qed.

Lemma binary_normalize_int' : forall mode m e zs,
    (Z.abs m < 2 ^ (prec - 1))%Z ->
    (e = 0)%Z ->
    B2R _ _ (binary_normalize _ _ Hprec Hprec_emax mode m e zs) =
    F2R (Float radix2 m e).
intros. destruct m.
- subst e. eapply binary_normalize_int_zero.
- eapply binary_normalize_int_pos; try assumption.
  unfold Z.abs in *. forward eapply (Zgt_pos_0 p). omega.
- eapply binary_normalize_int_neg; try assumption.
  rewrite Z.abs_neq in *; forward eapply (Zlt_neg_0 p); try omega.
Qed.

Lemma binary_normalize_int : forall mode m zs,
    (Z.abs m < 2 ^ (prec - 1))%Z ->
    B2R _ _ (binary_normalize _ _ Hprec Hprec_emax mode m 0 zs) =
    IZR m.
intros.
replace (IZR m) with (F2R (Float radix2 m 0)).
- eapply binary_normalize_int'; eauto.
- unfold F2R; simpl. rewrite Z2R_IZR. ring.
Qed.


Lemma Z_abs_range : forall z z_max, (0 <= Z.abs z < z_max)%Z <-> (-z_max < z < z_max)%Z.
intros. constructor; intro.
- destruct z; simpl in *; try omega.
  replace (Z.neg p) with (- Z.pos p)%Z by reflexivity.
  omega.
- destruct z; simpl in *.
  + omega.
  + forward eapply (Zgt_pos_0 p). omega.
  + forward eapply (Zlt_neg_0 p).
    replace (Z.pos p) with (- Z.neg p)%Z by reflexivity.
    omega.
Qed.


Definition fwhole (f : binary_float prec emax) :=
    whole (B2R _ _ f) /\ is_finite _ _ f = true.

Definition fwhole_eq (f : binary_float prec emax) z :=
    B2R _ _ f = IZR z /\ is_finite _ _ f = true.

Lemma fwhole_eq_whole : forall f z, fwhole_eq f z -> whole (B2R _ _ f).
intros ? ? [ HB2R Hfin ].
rewrite HB2R. eapply IZR_whole.
Qed.


Definition Z2B (z : Z) : binary_float prec emax :=
    binary_normalize prec emax Hprec Hprec_emax mode_NE z 0 false.

Lemma fwhole_eq_Z2B : forall z,
    (Z.abs z < 2 ^ (prec - 1))%Z ->
    fwhole_eq (Z2B z) z.
intros0 Habs.
split; unfold Z2B.
- eapply binary_normalize_int. assumption.
- forward refine (binary_normalize_correct prec emax Hprec Hprec_emax mode_NE z 0 false) as HH.
  rewrite no_overflow_int_bool' with (z := z) in HH; cycle 1.
  { unfold F2R. simpl. ring. }
  { eapply Z_abs_range. pose proof Z.abs_nonneg. eauto. }
  destruct HH as ( HB2R & Hfin & Hsign ).
  exact Hfin.
Qed.

Lemma fwhole_eq_Bcompare : forall (f1 f2 : binary_float prec emax) z1 z2,
    fwhole_eq f1 z1 ->
    fwhole_eq f2 z2 ->
    Bcompare _ _ f1 f2 = Some (Z.compare z1 z2).
intros ? ? ? ? (Heq1 & Hfin1) (Heq2 & Hfin2).

forward refine (Bcompare_correct prec emax f1 f2 Hfin1 Hfin2) as HH.
rewrite HH. f_equal.
rewrite Heq1, Heq2.
destruct (Rcompare (IZR _) (IZR _)) eqn:Hcmp.
- symmetry. rewrite Z.compare_eq_iff.
  eapply Rcompare_Eq_inv, eq_IZR in Hcmp.
  assumption.
- symmetry. rewrite Z.compare_lt_iff.
  eapply Rcompare_Lt_inv, lt_IZR in Hcmp.
  assumption.
- symmetry. rewrite Z.compare_gt_iff.
  eapply Rcompare_Gt_inv, Rgt_lt, lt_IZR in Hcmp.
  assumption.
Qed.

Lemma fwhole_eq_Bplus : forall (f1 f2 : binary_float prec emax) z1 z2 mode nan_thing,
    fwhole_eq f1 z1 ->
    fwhole_eq f2 z2 ->
    (0 <= Z.abs (z1 + z2) < 2 ^ (prec - 1))%Z ->
    fwhole_eq (Bplus _ _ Hprec Hprec_emax nan_thing mode f1 f2) (z1 + z2).
intros ? ? ? ? ? ? (Heq1 & Hfin1) (Heq2 & Hfin2) Habs.

forward refine (Bplus_correct prec emax Hprec Hprec_emax nan_thing mode f1 f2 Hfin1 Hfin2) as HH.
rewrite no_overflow_int_bool' with (z := (z1 + z2)%Z) in HH; cycle 1.
{ rewrite Heq1, Heq2. rewrite Z2R_IZR. eauto using plus_IZR. }
{ eapply Z_abs_range. assumption. }

destruct HH as ( HB2R & Hfin & Hsign ).
split; [ | assumption ].

rewrite HB2R.
unfold round, F2R, Fnum, Fexp. rewrite Z2R_IZR, whole_round_mode; cycle 1.
{ rewrite Heq1, Heq2, <- plus_IZR, <- Z2R_IZR.
  destruct (z1 + z2)%Z eqn:?.
  - unfold scaled_mantissa. simpl. rewrite Rmult_0_l.
    replace 0 with (IZR 0) by reflexivity. eapply IZR_whole.
  - simpl in Habs. forward eapply (Zgt_pos_0 p).
    eapply whole_scaled_mantissa. simpl. omega.
  - simpl in Habs. forward eapply (Zgt_pos_0 p).
    eapply whole_scaled_mantissa. simpl. omega. }

unfold scaled_mantissa. remember (canonic_exp _ _ _) as cexp.
rewrite Rmult_assoc, <- bpow_plus.
replace (- cexp + cexp)%Z with 0%Z by omega. simpl. rewrite Rmult_1_r.
rewrite Heq1, Heq2. eauto using plus_IZR.
Qed.

Lemma fwhole_eq_Bopp : forall (f1 : binary_float prec emax) z1 nan_thing,
    fwhole_eq f1 z1 ->
    fwhole_eq (Bopp _ _ nan_thing f1) (Z.opp z1).
intros ? ? ? (Heq1 & Hfin1).

forward refine (B2R_Bopp prec emax nan_thing f1).
unfold Bopp in *. destruct f1; try discriminate Hfin1.

- (* zero *)
  split; [ | reflexivity ].
  simpl in *. rewrite opp_IZR. congruence.

- (* finite *)
  split; [ | reflexivity ].
  rewrite opp_IZR. congruence.
Qed.

Lemma fwhole_eq_Bminus : forall (f1 f2 : binary_float prec emax) z1 z2 mode nan_thing,
    fwhole_eq f1 z1 ->
    fwhole_eq f2 z2 ->
    (0 <= Z.abs (z1 - z2) < 2 ^ (prec - 1))%Z ->
    fwhole_eq (Bminus _ _ Hprec Hprec_emax nan_thing mode f1 f2) (z1 - z2).
intros0 Heq1 Heq2 Habs.
unfold Bminus.
replace (z1 - z2)%Z with (z1 + -z2)%Z in * by omega.
eapply fwhole_eq_Bplus; eauto.
eapply fwhole_eq_Bopp; eauto.
Qed.

Lemma fwhole_eq_Bmult : forall (f1 f2 : binary_float prec emax) z1 z2 mode nan_thing,
    fwhole_eq f1 z1 ->
    fwhole_eq f2 z2 ->
    (0 <= Z.abs (z1 * z2) < 2 ^ (prec - 1))%Z ->
    fwhole_eq (Bmult _ _ Hprec Hprec_emax nan_thing mode f1 f2) (z1 * z2).
intros ? ? ? ? ? ? (Heq1 & Hfin1) (Heq2 & Hfin2) Habs.

forward refine (Bmult_correct prec emax Hprec Hprec_emax nan_thing mode f1 f2) as HH.
rewrite no_overflow_int_bool' with (z := (z1 * z2)%Z) in HH; cycle 1.
{ rewrite Heq1, Heq2. rewrite Z2R_IZR. eauto using mult_IZR. }
{ eapply Z_abs_range. assumption. }

destruct HH as ( HB2R & Hfin & Hsign ).
split; [ | eauto with bool ].

rewrite HB2R.
unfold round, F2R, Fnum, Fexp. rewrite Z2R_IZR, whole_round_mode; cycle 1.
{ rewrite Heq1, Heq2, <- mult_IZR, <- Z2R_IZR.
  destruct (z1 * z2)%Z eqn:?.
  - unfold scaled_mantissa. simpl. rewrite Rmult_0_l.
    replace 0 with (IZR 0) by reflexivity. eapply IZR_whole.
  - simpl in Habs. forward eapply (Zgt_pos_0 p).
    eapply whole_scaled_mantissa. simpl. omega.
  - simpl in Habs. forward eapply (Zgt_pos_0 p).
    eapply whole_scaled_mantissa. simpl. omega. }

unfold scaled_mantissa. remember (canonic_exp _ _ _) as cexp.
rewrite Rmult_assoc, <- bpow_plus.
replace (- cexp + cexp)%Z with 0%Z by omega. simpl. rewrite Rmult_1_r.
rewrite Heq1, Heq2. eauto using mult_IZR.
Qed.



Definition B2Z_trunc (b : binary_float prec emax) : Z :=
    FF2Z_trunc (B2FF _ _ b).

Definition B2Z_safe (b : binary_float prec emax) : option Z :=
    FF2Z_safe (B2FF _ _ b).

Lemma Ns2Z_cond_Zopp : forall n s, Ns2Z n s = cond_Zopp s (Z.of_N n).
intros; destruct n; destruct s; simpl; reflexivity.
Qed.

Lemma B2Z_safe_correct' : forall (f : binary_float prec emax) z,
    B2Z_safe f = Some z -> B2R _ _ f = IZR z.
intros0 Heq.
destruct f.

- (* zero *)
  unfold B2Z_safe, B2FF, FF2Z_safe in Heq.
  inversion Heq. subst z. simpl. reflexivity.

- (* infinity *)
  unfold B2Z_safe, B2FF, FF2Z_safe in Heq.
  congruence.

- (* nan *)
  unfold B2Z_safe, B2FF, FF2Z_safe in Heq.
  destruct n. congruence.

- (* finite *)
  unfold B2Z_safe, B2FF, FF2Z_safe, FF2Z_safe_aux in Heq.
  destruct e.

  + (* e = 0 *)
    inversion Heq. subst z.
    unfold B2R, F2R, Fnum, Fexp, cond_Zopp, Z.opp, bpow.
    rewrite Z2R_IZR. ring.

  + (* e > 0 *)
    match type of Heq with Some ?x = Some ?y => assert (x = y) by congruence end.
    unfold B2R, F2R, Fnum, Fexp.
    subst z. rewrite N.shiftl_mul_pow2.
    destruct b; rewrite Ns2Z_cond_Zopp; unfold cond_Zopp; rewrite Z2R_IZR.
    --  (* b = true *)
        rewrite N2Z.inj_mul, N2Z.inj_pow.
        unfold bpow. rewrite Z2R_IZR, Z.pow_pos_fold. fold (Z.of_N (N.pos p)).
        repeat rewrite opp_IZR.
        rewrite mult_IZR, <- (N_nat_Z (N.pos p)).
        repeat rewrite <- pow_IZR. simpl. ring.
    --  (* b = false *)
        rewrite N2Z.inj_mul, N2Z.inj_pow.
        unfold bpow. rewrite Z2R_IZR, Z.pow_pos_fold. fold (Z.of_N (N.pos p)).
        rewrite mult_IZR, <- (N_nat_Z (N.pos p)).
        repeat rewrite <- pow_IZR. simpl. ring.

  + (* e < 0 *)
    destruct (N.land _ _ =? 0)%N eqn:Hland; try congruence.
    rewrite N.eqb_eq in Hland.
    match type of Heq with Some ?x = Some ?y => assert (x = y) by congruence end.
    unfold B2R, F2R, Fnum, Fexp.
    subst z.
    rewrite Ns2Z_cond_Zopp, nshiftr_zshiftr_pos.
    destruct b; unfold cond_Zopp; repeat rewrite Z2R_IZR.
    --  (* b = true *)
        repeat rewrite opp_IZR. rewrite shiftr_IZR_pos by assumption.
        unfold bpow. rewrite Z2R_IZR. unfold radix2, radix_val. ring.
    --  (* b = false *)
        repeat rewrite opp_IZR. rewrite shiftr_IZR_pos by assumption.
        unfold bpow. rewrite Z2R_IZR. unfold radix2, radix_val. ring.
Qed.

Lemma B2Z_safe_correct : forall f z,
    B2Z_safe f = Some z -> fwhole_eq f z.
intros0 Heq. split.
- eapply B2Z_safe_correct'. assumption.
- destruct f; simpl; try congruence.
  + compute in Heq. congruence.
  + unfold B2Z_safe, FF2Z_safe, B2FF in Heq. destruct n. congruence.
Qed.

Lemma N2Z_inj_land : forall n m, Z.of_N (N.land n m) = Z.land (Z.of_N n) (Z.of_N m).
intros. destruct n, m; simpl; reflexivity.
Qed.

Lemma N2Z_inj_shiftl : forall n m, Z.of_N (N.shiftl n m) = Z.shiftl (Z.of_N n) (Z.of_N m).
intros. destruct n, m; try reflexivity.
- simpl. induction p; simpl.
  + rewrite <- IHp, <- IHp. reflexivity.
  + rewrite <- IHp, <- IHp. reflexivity.
  + reflexivity.
- simpl. generalize p. induction p0; intros; simpl.
  + rewrite <- IHp0, <- IHp0. reflexivity.
  + rewrite <- IHp0, <- IHp0. reflexivity.
  + reflexivity.
Qed.

Lemma N2Z_inj_ones : forall n, Z.of_N (N.ones n) = Z.ones (Z.of_N n).
intros. destruct n.
{ compute. reflexivity. }
unfold N.ones, Z.ones.
rewrite N2Z.inj_pred; cycle 1.
{ destruct (N.shiftl _ _) eqn:Heq.
  - rewrite N.shiftl_eq_0_iff in Heq. congruence.
  - constructor. }
rewrite N2Z_inj_shiftl. simpl. reflexivity.
Qed.

Lemma B2Z_safe_complete : forall f z,
    fwhole_eq f z ->
    B2Z_safe f = Some z.
intros ? ? [ Heq Hfin ].
destruct (B2Z_safe f) eqn:Heq'.
{ eapply B2Z_safe_correct in Heq'. destruct Heq' as [ Heq' Hfin' ].
  rewrite Heq in Heq'. eapply eq_IZR in Heq'. congruence. }

unfold B2Z_safe, FF2Z_safe, B2FF in Heq'.
destruct f eqn:?.
{ (* zero *) congruence. }
{ (* infinite *) simpl in Hfin. congruence. }
{ (* nan *) simpl in Hfin. congruence. }

unfold FF2Z_safe_aux in Heq'.
destruct e eqn:?.
{ (* e = 0 *) congruence. }
{ (* e > 0 *) congruence. }

(* e < 0 *)
destruct (N.land _ _ =? _)%N eqn:Hland.
{ (* N.land _ _ = 0 *) congruence. }

rewrite N.eqb_neq in Hland.
unfold B2R, F2R in Heq. simpl in Heq.
eapply (Rmult_eq_compat_r (Z2R (Z.pow_pos 2 p))) in Heq.
rewrite Rmult_assoc, <- Rinv_l_sym, Rmult_1_r in Heq; cycle 1.
{ rewrite Z.pow_pos_fold.
  forward eapply (Z.pow_pos_nonneg 2 (Z.pos p)).
  { omega. }
  { forward eapply (Zgt_pos_0 p). omega. }
  replace 0 with (IZR 0) by reflexivity.
  rewrite Z2R_IZR. intro Hbad. eapply eq_IZR in Hbad. omega. }

(* mangle Heq to get a better version *)
repeat rewrite Z2R_IZR in Heq. rewrite <- mult_IZR in Heq. eapply eq_IZR in Heq.
assert (Heq_fixed : (exists n, N.pos m = n * 2 ^ N.pos p)%N).
{ assert (HZeq_abs : forall n m, n = m -> Z.abs n = Z.abs m) by (intros; congruence).
  eapply HZeq_abs in Heq. clear HZeq_abs.
  rewrite abs_cond_Zopp in Heq. simpl in Heq.
  rewrite Z.abs_mul, Z.pow_pos_fold, Z.abs_pow in Heq. simpl in Heq.

  replace (Z.pos m) with (Z.of_N (N.pos m)) in Heq by reflexivity.
  replace (Z.pow_pos 2 p) with (Z.of_N (2 ^ N.pos p)) in Heq; cycle 1.
  { rewrite N2Z.inj_pow. simpl. reflexivity. }

  destruct z as [ | q | q ]; try unfold Z.abs in Heq.
  - destruct b; simpl in Heq; congruence.
  - exists (N.pos q). 
    replace (Z.pos q) with (Z.of_N (N.pos q)) in Heq by reflexivity.
    rewrite <- N2Z.inj_mul in Heq. eapply N2Z.inj in Heq.
    assumption.
  - exists (N.pos q). 
    replace (Z.pos q) with (Z.of_N (N.pos q)) in Heq by reflexivity.
    rewrite <- N2Z.inj_mul in Heq. eapply N2Z.inj in Heq.
    assumption. }
clear Heq. destruct Heq_fixed as [ n Heq ].

rewrite Heq in Hland.
contradict Hland.
rewrite N.land_ones.
eapply N.mod_mul.
eapply N.pow_nonzero.
discriminate.
Qed.

End binary_float.


Definition Z2B64 := @Z2B 53 1024 ltac:(omega) ltac:(omega).

Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Omega.

Require Import v1.Multi.
Require Import v1.NeutronTactics.

Require Import ProofIrrelevance.

Set Default Timeout 10.
Set Implicit Arguments.


Inductive no_dup_index n : list (index n) -> Prop :=
| NdiNil : no_dup_index []
| NdiCons : forall i l,
        Forall (fun i' => index_nat i <> index_nat i') l ->
        no_dup_index l ->
        no_dup_index (i::l).

Inductive sorted_index n : list (index n) -> Prop :=
| SiNil : sorted_index []
| SiCons : forall i l,
        Forall (fun i' => index_nat i < index_nat i') l ->
        sorted_index l ->
        sorted_index (i::l).

Lemma index_list'_sorted :
    forall n i acc Hlt,
    sorted_index acc ->
    Forall (fun i' => i < index_nat i') acc ->
    sorted_index (@index_list' n i acc Hlt).
first_induction i; unfold index_list'; fold index_list'; intros0 Hndi Hfa.
{ (* zero *) constructor; simpl; assumption. }

eapply IHi.
- constructor; simpl; eassumption.
- eapply Forall_cons; simpl.
  + omega.
  + eapply Forall_forall. intros i' Hi'.
    rewrite Forall_forall in Hfa.
    specialize (Hfa i' Hi').
    omega.
Qed.

Lemma sorted_index_no_dup :
    forall n (l : list (index n)),
    sorted_index l -> no_dup_index l.
first_induction l; intros.
{ constructor. }

inversion H; subst.
constructor.
- eapply Forall_impl; eauto.
  simpl. intros. omega.
- eauto.
Qed.

Lemma index_list_no_dup :
    forall n, no_dup_index (index_list n).
intros.
destruct n; unfold index_list.
{ unfold index_list. constructor. }
eapply sorted_index_no_dup.
eapply index_list'_sorted.
- constructor.
- eauto.
Qed.

Lemma no_dup_tail :
    forall n (x : index n) xs,
    no_dup_index (x :: xs) ->
    no_dup_index xs.
intros0 Hdiff. inversion Hdiff. eauto.
Qed.

Lemma no_dup_cons_nat :
    forall n (x x' : index n) xs,
    In x' xs ->
    no_dup_index (x :: xs) ->
    index_nat x <> index_nat x'.
intros0 Hin Hdiff.
inversion Hdiff; subst.
rewrite Forall_forall in *. eauto.
Qed.



Lemma index_list'_length : forall n i acc Hlt,
    length (@index_list' n i acc Hlt) = length acc + S i.
first_induction i; intros; simpl in *.
- omega.
- rewrite IHi. simpl. omega.
Qed.

Lemma index_list_length : forall n,
    length (index_list n) = n.
intros. destruct n.
unfold index_list.
- reflexivity.
- eapply index_list'_length.
Qed.



Lemma index_list'_nth_error_nat : forall n i acc Hlt,
    (forall j idx,
        nth_error acc j = Some idx ->
        index_nat idx = S i + j) ->
    (forall j idx,
        nth_error (@index_list' n i acc Hlt) j = Some idx ->
        index_nat idx = j).
first_induction i; intros0 Hacc; intros0 Hnth; simpl in *.
- destruct j; simpl in *.
  + inject_some. simpl. reflexivity.
  + eapply Hacc. auto.
- eapply IHi; eauto. intros.
  destruct j0; simpl in *.
  + inject_some. simpl. omega.
  + replace (i + S j0) with (S (i + j0)) by omega.
    eapply Hacc. auto.
Qed.

Lemma index_list_nth_error_nat : forall n i idx,
    nth_error (index_list n) i = Some idx ->
    index_nat idx = i.
destruct n; intros.
  { simpl in *. destruct i; discriminate. }
eapply index_list'_nth_error_nat; eauto.
intros. destruct j; discriminate.
Qed.



Lemma index_proof_irrel : forall n (i1 i2 : index n),
    index_nat i1 = index_nat i2 <-> i1 = i2.
intros. split; intro; destruct i1, i2; simpl in *.
- subst. f_equal. apply proof_irrelevance.
- invc H. reflexivity.
Qed.

Lemma index_list_in : forall n (i : index n),
    In i (index_list n).
intros.
destruct i as [i' Hlt].
eapply nth_error_In with (n := i').
destruct (nth_error _ _) eqn:?; cycle 1.
  { rewrite nth_error_None in *. rewrite index_list_length in *. omega. }
forward eapply index_list_nth_error_nat; eauto.
f_equal. eapply index_proof_irrel.
simpl. auto.
Qed.

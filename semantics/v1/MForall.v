Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Omega.

Require Import v1.NeutronTactics.
Require Import v1.Util.

Require Import v1.Multi.
Require Import v1.ListLemmas.

Set Default Timeout 5.



Fixpoint MForall' {n} {A : Set} (P : A -> Prop) : multi' n A -> Prop :=
    match n as n_ return multi' n_ A -> Prop with
    | 0 => fun m =>
            let x := m in
            P m
    | S n => fun m =>
            let '(m', x) := m in
            MForall' P m' /\ P x
    end.

Definition MForall {n} {A : Set} (P : A -> Prop) : multi n A -> Prop :=
    match n as n_ return multi n_ A -> Prop with
    | 0 => fun _ => True
    | S n' => MForall' P
    end.


Lemma rep_MForall' : forall n (A : Set) (P : A -> Prop) v,
    P v ->
    MForall' P (multi'_rep n v).
induction n; intros0 Hv.
- assumption.
- constructor; eauto.
Qed.

Lemma MForall'_get : forall n (A : Set) (P : A -> Prop) (x : multi' n A) i,
    MForall' P x ->
    P (multi'_get x i).
induction n; intros0 Hfa.
- destruct i as [i' Hlt]. destruct i'; try solve [exfalso; omega].
  simpl. assumption.
- destruct i as [i' Hlt]. 
  simpl. break_match.
  + destruct x. destruct Hfa. auto.
  + destruct x. destruct Hfa. simpl.
    eapply IHn. eassumption.
Qed.

Lemma set_MForall' : forall n (A : Set) (P : A -> Prop) (x : multi' n A) i v,
    MForall' P x ->
    P v ->
    MForall' P (multi'_set x i v).
induction n; intros0 Hfa Hv.
- destruct i as [i' Hlt]. destruct i'; try solve [exfalso; omega].
  simpl. assumption.
- destruct i as [i' Hlt].
  simpl. break_match. break_match.
  + destruct x, Hfa. simpl in *. inject_pair. auto.
  + destruct x, Hfa. simpl in *. inject_pair. auto.
Qed.

Definition MForall'_dec : forall n (A : Set) (P : A -> Prop) (x : multi' n A),
    (forall v, { P v } + { ~ P v }) ->
    { MForall' P x } + { ~ MForall' P x }.
induction n; intros0 P_dec.
- eapply P_dec.
- destruct x as [x' v].
  destruct (P_dec v); cycle 1.
    { right. inversion 1. auto. }
  destruct (IHn _ _ x' P_dec); cycle 1.
    { right. inversion 1. auto. }
  left. constructor; eauto.
Defined.


Lemma rep_MForall : forall n (A : Set) (P : A -> Prop) v,
    P v ->
    MForall P (multi_rep n v).
destruct n.
- intros. constructor.
- eapply rep_MForall'.
Qed.

Lemma MForall_get : forall n (A : Set) (P : A -> Prop) (x : multi n A) i,
    MForall P x ->
    P (multi_get x i).
destruct n.
- intros. destruct i. exfalso. omega.
- eapply MForall'_get.
Qed.

Lemma set_MForall : forall n (A : Set) (P : A -> Prop) (x : multi n A) i v,
    MForall P x ->
    P v ->
    MForall P (multi_set x i v).
destruct n.
- intros. constructor.
- eapply set_MForall'.
Qed.

Definition MForall_dec : forall n (A : Set) (P : A -> Prop) (x : multi n A),
    (forall v, { P v } + { ~ P v }) ->
    { MForall P x } + { ~ MForall P x }.
destruct n.
- intros. left. constructor.
- eapply MForall'_dec.
Defined.



Fixpoint MForall2' {n} {A B : Set} (P : A -> B -> Prop) : multi' n A -> multi' n B -> Prop :=
    match n as n_ return multi' n_ A -> multi' n_ B -> Prop with
    | 0 => fun x y =>
            let xv := x in
            let yv := y in
            P xv yv
    | S n => fun x y =>
            let '(x', xv) := x in
            let '(y', yv) := y in
            MForall2' P x' y' /\ P xv yv
    end.

Definition MForall2 {n} {A B : Set} (P : A -> B -> Prop) : multi n A -> multi n B -> Prop :=
    match n as n_ return multi n_ A -> multi n_ B -> Prop with
    | 0 => fun _ _ => True
    | S n' => MForall2' P
    end.


Lemma rep_MForall2' : forall n (A B : Set) (P : A -> B -> Prop) xv yv,
    P xv yv ->
    MForall2' P (multi'_rep n xv) (multi'_rep n yv).
induction n; intros0 Hv.
- assumption.
- constructor; eauto.
Qed.

Lemma MForall2'_get : forall n (A B : Set) (P : A -> B -> Prop)
        (x : multi' n A) (y : multi' n B) i,
    MForall2' P x y ->
    P (multi'_get x i) (multi'_get y i).
induction n; intros0 Hfa.
- destruct i as [i' Hlt]. destruct i'; try solve [exfalso; omega].
  simpl. assumption.
- destruct i as [i' Hlt]. 
  simpl. break_match.
  + destruct x, y, Hfa. auto.
  + destruct x, y, Hfa.  eapply IHn. eassumption.
Qed.

Lemma set_MForall2' : forall n (A B : Set) (P : A -> B -> Prop)
        (x : multi' n A) (y : multi' n B) i xv yv,
    MForall2' P x y ->
    P xv yv ->
    MForall2' P (multi'_set x i xv) (multi'_set y i yv).
induction n; intros0 Hfa Hv.
- destruct i as [i' Hlt]. destruct i'; try solve [exfalso; omega].
  simpl. assumption.
- destruct i as [i' Hlt].
  simpl. do 3 break_match.
  + destruct x, y, Hfa. simpl in *. inject_pair. auto.
  + destruct x, y, Hfa. simpl in *. inject_pair. auto.
Qed.

Definition MForall2'_dec : forall n (A B : Set) (P : A -> B -> Prop)
        (x : multi' n A) (y : multi' n B),
    (forall xv yv, { P xv yv } + { ~ P xv yv }) ->
    { MForall2' P x y } + { ~ MForall2' P x y }.
induction n; intros0 P_dec.
- eapply P_dec.
- destruct x as [x' xv], y as [y' yv].
  destruct (P_dec xv yv); cycle 1.
    { right. inversion 1. auto. }
  destruct (IHn _ _ _ x' y' P_dec); cycle 1.
    { right. inversion 1. auto. }
  left. constructor; eauto.
Defined.


Lemma rep_MForall2 : forall n (A B : Set) (P : A -> B -> Prop) xv yv,
    P xv yv ->
    MForall2 P (multi_rep n xv) (multi_rep n yv).
destruct n.
- intros. constructor.
- eapply rep_MForall2'.
Qed.

Lemma MForall2_get : forall n (A B : Set) (P : A -> B -> Prop)
        (x : multi n A) (y : multi n B) i,
    MForall2 P x y ->
    P (multi_get x i) (multi_get y i).
destruct n.
- intros. destruct i. exfalso. omega.
- eapply MForall2'_get.
Qed.

Lemma set_MForall2 : forall n (A B : Set) (P : A -> B -> Prop)
        (x : multi n A) (y : multi n B) i xv yv,
    MForall2 P x y ->
    P xv yv ->
    MForall2 P (multi_set x i xv) (multi_set y i yv).
destruct n.
- intros. constructor.
- eapply set_MForall2'.
Qed.

Definition MForall2_dec : forall n (A B : Set) (P : A -> B -> Prop)
        (x : multi n A) (y : multi n B),
    (forall xv yv, { P xv yv } + { ~ P xv yv }) ->
    { MForall2 P x y } + { ~ MForall2 P x y }.
destruct n.
- intros. left. constructor.
- eapply MForall2'_dec.
Defined.



Lemma multi'_to_list'_in_acc : forall n A (x : multi' n A) acc a,
    In a acc ->
    In a (multi'_to_list' n A x acc).
induction n; intros0 Hin; simpl in *.
- eauto.
- destruct x. simpl in *. eapply IHn. simpl. eauto.
Qed.


Lemma MForall'_list'_Forall : forall n (A : Set) (P : A -> Prop) (x : multi' n A) acc,
    Forall P acc ->
    MForall' P x <-> Forall P (multi'_to_list' n A x acc).
induction n; intros0 Hacc; simpl in *; split; intro HH.
- eauto.
- invc HH. eauto.
- break_match. break_and. simpl. rewrite <- IHn; eauto.
- break_match. simpl in *.
  assert (P a).
    { rewrite Forall_forall in HH. eapply HH.
      eapply multi'_to_list'_in_acc. simpl. eauto. }
  split; eauto.
  rewrite IHn; eauto.
Qed.

Lemma MForall'_Forall : forall n (A : Set) (P : A -> Prop) (x : multi' n A),
    MForall' P x <-> Forall P (multi'_to_list x).
intros. eapply MForall'_list'_Forall; eauto.
Qed.

Lemma MForall_Forall : forall n (A : Set) (P : A -> Prop) (x : multi n A),
    MForall P x <-> Forall P (multi_to_list x).
destruct n; intros.
- destruct x. simpl. intuition.
- simpl. eapply MForall'_Forall.
Qed.


Lemma multi'_to_list'_nth_error_acc : forall n A (x : multi' n A) acc i,
    i >= S n ->
    nth_error (multi'_to_list' n A x acc) i = nth_error acc (i - S n).
induction n; intros; simpl in *.
- destruct i; [ exfalso; omega | ]. simpl in *.
  replace (i - 0) with i by omega. reflexivity.
- destruct x. simpl in *.
  rewrite IHn.
  + replace (i - S n) with (S (i - S (S n))) by omega.
    simpl. reflexivity.
  + omega.
Qed.

Lemma MForall2'_list'_Forall2 : forall n (A B : Set) (P : A -> B -> Prop)
        (x : multi' n A) (y : multi' n B) acc1 acc2,
    Forall2 P acc1 acc2 ->
    MForall2' P x y <->
        Forall2 P (multi'_to_list' n A x acc1) (multi'_to_list' n B y acc2).
induction n; intros0 Hacc; simpl in *; split; intro HH.
- eauto.
- invc HH. eauto.
- do 2 break_match. break_and. simpl. rewrite <- IHn; eauto.
- do 2 break_match. simpl in *.
  assert (P a b).
    { eapply Forall2_nth_error with (i := S n); eauto.
      - erewrite multi'_to_list'_nth_error_acc; eauto.
        replace (S n - S n) with 0 by omega. reflexivity.
      - erewrite multi'_to_list'_nth_error_acc; eauto.
        replace (S n - S n) with 0 by omega. reflexivity. }
  split; eauto.
  rewrite IHn; eauto.
Qed.

Lemma MForall2'_Forall2 : forall n (A B : Set) (P : A -> B -> Prop)
        (x : multi' n A) (y : multi' n B),
    MForall2' P x y <-> Forall2 P (multi'_to_list x) (multi'_to_list y).
intros. eapply MForall2'_list'_Forall2; eauto.
Qed.

Lemma MForall2_Forall2 : forall n (A B : Set) (P : A -> B -> Prop)
        (x : multi n A) (y : multi n B),
    MForall2 P x y <-> Forall2 P (multi_to_list x) (multi_to_list y).
destruct n; intros.
- destruct x, y. simpl. intuition.
- simpl. eapply MForall2'_Forall2.
Qed.


Lemma MForall'_forall : forall n (A : Set) (P : A -> Prop) (x : multi' n A),
    MForall' P x <-> (forall i val, multi'_get x i = val -> P val).
induction n; intros.
- simpl.  assert (index 1) by (mk_index 0).
  split; intros; [ congruence | auto ].
- destruct x as [x val]. split; intros.
  + destruct i as [i Hlt]. on >@MForall', invc.
    unfold multi'_get; fold multi'_get. break_match; auto; simpl.
    rewrite IHn in *. on _, eapply_. reflexivity.
  + split.
    * rewrite IHn. intros.
      destruct i as [i Hlt].
      on _, eapply_.  unfold multi'_get. fold multi'_get.
      instantiate (1 := ltac:(mk_index i)). cbv iota beta. break_match; [ omega | ].
      simpl. erewrite multi'_get_eq; eauto.
    * on _, eapply_.
      instantiate (1 := ltac:(mk_index (S n))). simpl. break_match; try congruence.
Qed.

Lemma MForall_forall : forall n (A : Set) (P : A -> Prop) (x : multi n A),
    MForall P x <-> (forall i val, multi_get x i = val -> P val).
destruct n; intros.
- destruct x. simpl. intuition.  destruct i as [i Hlt]. omega.
- simpl. eapply MForall'_forall.
Qed.


Lemma MForall2'_forall : forall n (A B : Set) (P : A -> B -> Prop)
        (x : multi' n A) (y : multi' n B),
    MForall2' P x y <-> (forall i xv yv,
        multi'_get x i = xv ->
        multi'_get y i = yv ->
        P xv yv).
induction n; intros.
- simpl.  assert (index 1) by (mk_index 0).
  split; intros; [ congruence | auto ].
- destruct x as [x xv], y as [y yv]. split; intros.
  + destruct i as [i Hlt]. on >@MForall2', invc.
    unfold multi'_get; fold multi'_get. break_match; auto; simpl.
    rewrite IHn in *. on _, eapply_; reflexivity.
  + split.
    * rewrite IHn. intros.
      destruct i as [i Hlt].
      on _, eapply_;  unfold multi'_get; fold multi'_get.
      instantiate (1 := ltac:(mk_index i)).
      all: cbv iota beta; break_match; [ omega | ].
      all: simpl; erewrite multi'_get_eq; eauto.
    * on _, eapply_.
      instantiate (1 := ltac:(mk_index (S n))).
      all: simpl; break_match; try congruence.
Qed.

Lemma MForall2_forall : forall n (A B : Set) (P : A -> B -> Prop)
        (x : multi n A) (y : multi n B),
    MForall2 P x y <-> (forall i xv yv,
        multi_get x i = xv ->
        multi_get y i = yv ->
        P xv yv).
destruct n; intros.
- destruct x. simpl. intuition.  destruct i as [i Hlt]. omega.
- simpl. eapply MForall2'_forall.
Qed.

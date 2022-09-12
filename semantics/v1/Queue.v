Require Import Arith.
Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import Sorted.
Require Import Omega.

Require Import v1.Step.
Require Import v1.NeutronTactics.

Open Scope Z_scope.


Definition time := Z.

Record timestamped_event := TsEvent {
    te_when : time;
    te_evt : input_event
}.


Definition te_le := fun te1 te2 => te_when te1 <= te_when te2.

Lemma te_le_refl : forall te, te_le te te.
intros. unfold te_le. omega.
Qed.
Hint Resolve te_le_refl.


Record queue := Queue {
    q_list : list timestamped_event;
    q_sorted : StronglySorted te_le q_list
}.

Definition queue_empty : queue.
refine (Queue [] _).
constructor.
Defined.

Fixpoint q_list_insert te lst : list timestamped_event :=
    match lst with
    | [] => [te]
    | x :: xs =>
            if Z_le_dec (te_when x) (te_when te)
                then x :: q_list_insert te xs
                else te :: x :: xs
    end.

Lemma q_list_insert_hd : forall te lst,
    exists x xs,
        q_list_insert te lst = x :: xs /\
        te_le x te.
first_induction lst; intros; simpl.
{ do 2 eexists. split; eauto. }

break_if.
- do 2 eexists; split; eauto.
- do 2 eexists; split; eauto.
Qed.

Lemma q_list_insert_in : forall te lst x,
    In x (q_list_insert te lst) ->
    x = te \/ In x lst.
first_induction lst; intros0 Hin; simpl in *.
{ firstorder. }

break_if.
- destruct Hin.
  + eauto.
  + forward eapply IHlst as HH; eauto.
    destruct HH; eauto.
- destruct Hin as [ ? | [ ? | ? ] ]; eauto.
Qed.

Lemma q_list_insert_preserves_sorted : forall te lst,
    StronglySorted te_le lst ->
    StronglySorted te_le (q_list_insert te lst).
first_induction lst; intros0 Hsort.
{ simpl. repeat constructor. }

simpl. break_if.
- constructor.
  { (* tail sorted *) eapply IHlst. invcs Hsort. assumption. }

  rewrite Forall_forall. intros te' Hin.
  forward eapply q_list_insert_in as HH; eauto. destruct HH.
    { (* te' = te *) unfold te_le. congruence. }
  invcs Hsort. on _, fun H => rewrite Forall_forall in H. eauto.

- constructor.
  { (* tail sorted *) assumption. }

  assert (te_when te <= te_when a) by omega.
  rewrite Forall_forall. intros te' Hin.
  assert (te_le a te').
    { invcs Hsort. on _, fun H => rewrite Forall_forall in H. eauto.
      destruct Hin; subst; eauto. }
  unfold te_le in *. omega.

Qed.

Definition queue_insert te q :=
    Queue (q_list_insert te (q_list q))
          (q_list_insert_preserves_sorted te (q_list q) (q_sorted q)).

Lemma queue_insert_q_list : forall te q,
    q_list (queue_insert te q) = q_list_insert te (q_list q).
intros.
reflexivity.
Qed.


Definition q_list_remove (lst : list timestamped_event) :=
    match lst with
    | [] => None
    | x :: xs => Some (x, xs)
    end.

Lemma q_list_remove_smallest : forall lst x lst',
    StronglySorted te_le lst ->
    q_list_remove lst = Some (x, lst') ->
    Forall (te_le x) lst'.
intros0 Hsort Hrm.
destruct lst; simpl in *; try discriminate.
invc Hsort. congruence.
Qed.

Lemma q_list_remove_none : forall lst,
    q_list_remove lst = None <-> lst = [].
intros. destruct lst; simpl; split; intro; congruence.
Qed.

Definition queue_remove (q : queue) : option (timestamped_event * queue).
destruct q as [lst Hsort].
destruct (q_list_remove lst) as [ [te lst'] | ] eqn:Heq; [ | exact None ].
refine (Some (te, Queue lst' _)).
hide.
invc Hsort.
  { simpl in *. discriminate. }
simpl in *. congruence.
Defined.

Lemma queue_remove_q_list : forall q,
    queue_remove q = None <-> q_list_remove (q_list q) = None.
intros. destruct q as [lst ?]; simpl.
destruct lst; simpl.
- split; intro; reflexivity.
- split; intro; discriminate.
Qed.

Lemma queue_remove_none : forall q,
    queue_remove q = None <-> q_list q = [].
intros.
rewrite queue_remove_q_list.
rewrite q_list_remove_none.
split; eauto.
Qed.

Lemma queue_remove_smallest : forall q x q',
    queue_remove q = Some (x, q') ->
    Forall (te_le x) (q_list q).
intros0 Hrm. destruct q as [lst Hsort]. destruct q' as [lst' Hsort'].
destruct lst; try discriminate. simpl in *.
fancy_injr <- Hrm. invc Hsort. constructor; eauto.
Qed.


Definition q_list_remove_bounded lst max :=
    match lst with
    | [] => inr lst
    | x :: xs =>
            if Z_le_dec (te_when x) max then
                inl (x, xs)
            else
                inr lst
    end.

Lemma q_list_remove_bounded_inl : forall lst max te' lst',
    q_list_remove_bounded lst max = inl (te', lst') ->
    lst = te' :: lst'.
intros0 Heq.
destruct lst; simpl in *; try congruence.
break_if; simpl in *; try congruence.
Qed.

Lemma q_list_remove_bounded_inr : forall lst max lst',
    q_list_remove_bounded lst max = inr lst' ->
    lst = lst'.
intros0 Heq.
destruct lst; simpl in *; try congruence.
break_if; simpl in *; try congruence.
Qed.

Definition queue_remove_bounded (q : queue) (max : time) : timestamped_event * queue + queue.
destruct q as [lst Hsort].
destruct (q_list_remove_bounded lst max) as [ [te' lst'] | lst' ] eqn:?.

- (* inl *)
  refine (inl (te', Queue lst' _)). hide.
  forward eapply q_list_remove_bounded_inl; eauto.
  invc Hsort; congruence.

- (* inr *)
  refine (inr (Queue lst' _)). hide.
  forward eapply q_list_remove_bounded_inr; eauto.
  congruence.
Defined.

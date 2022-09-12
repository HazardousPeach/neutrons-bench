Require Import List.
Import ListNotations.
Require Import v1.NeutronTactics.

Lemma not_exists : forall A P, (forall x : A, ~ P x) -> ~ exists x : A, P x.
firstorder.
Qed.

(* Tactic for proving that something doesn't exist.
 * Turns [ |- ~ exists x : A, P x ] into [ x : A |- ~ P x ]. *)
Ltac dne :=
    match goal with
    | [ |- ~ exists (x : ?T), _ ] =>
            let x' := fresh x in
            eapply not_exists; intro x';
            dne
    | [ |- _ ] => idtac
    end.

Lemma exists_implies : forall A (P Q : A -> Prop),
    (exists x, P x) ->
    (forall x, P x -> Q x) ->
    (exists x, Q x).
intros ? ? ? Hex ?. destruct Hex. eauto.
Qed.
Hint Resolve exists_implies.

Lemma not_exists_implies : forall A (P Q : A -> Prop),
    (~ exists x, Q x) ->
    (forall x, P x -> Q x) ->
    (~ exists x, P x).
intros; dne; eauto.
Qed.
Hint Resolve not_exists_implies.

Ltac not_inv := let H := fresh "H" in intro H; inversion H.

(* A common pattern: We wish to prove `~ exists x, P x` and we have in our
 * context `~ exists x, Q x`, where `P x` implies `Q x` by inversion. *)
Ltac dne_inv :=
    dne; not_inv; eauto.


Definition bind_option {A B : Type} (m : option A) (k : A -> option B) : option B :=
    match m with
    | Some x => k x
    | None => None
    end.

Notation "x '>>=' f" := (bind_option x f)
    (at level 42, left associativity).

Notation "'do' x '<-' m ';;' k" := (bind_option m (fun x => k))
    (at level 200, x ident, right associativity).

Ltac break_bind_option :=
    repeat match goal with
    | [ H : bind_option ?x _ = Some _ |- _ ] =>
            destruct x eqn:?; [ simpl in H | discriminate H ]
    end.


(* Two-value version of `sig` *)

Set Implicit Arguments.

Inductive sigp (A B : Type) (P : A -> B -> Prop) : Type :=
    existp : forall (x : A) (y : B), P x y -> sigp P.

Arguments sigp (A B P)%type.

Reserved Notation "{ x , y | P }" (at level 0, x at level 99, y at level 99).
Reserved Notation "{ x : A , y : B | P }" (at level 0, x at level 99, y at level 99).

Notation "{ x , y |  P }" := (sigp (fun x y => P)) : type_scope.
Notation "{ x : A , y : B  |  P }" := (sigp (A:=A) (B:=B) (fun x y => P)) : type_scope.

Add Printing Let sigp.

Unset Implicit Arguments.



Section assoc.
  Local Set Implicit Arguments.

  Variable K V : Type.
  Variable K_eq_dec : forall k k' : K, {k = k'} + {k <> k'}.

  Fixpoint assoc (l : list (K * V)) (k : K) : option V :=
    match l with
      | [] => None
      | (k', v) :: l' =>
        if K_eq_dec k k' then
          Some v
        else
          assoc l' k
    end.

  Definition assoc_default (l : list (K * V)) (k : K) (default : V) : V :=
    match (assoc l k) with
      | Some x => x
      | None => default
    end.

  Fixpoint assoc_set (l : list (K * V)) (k : K) (v : V) : list (K * V) :=
    match l with
      | [] => [(k, v)]
      | (k', v') :: l' =>
        if K_eq_dec k k' then
          (k, v) :: l'
        else
          (k', v') :: (assoc_set l' k v)
    end.

  Fixpoint assoc_del (l : list (K * V)) (k : K) : list (K * V) :=
    match l with
      | [] => []
      | (k', v') :: l' =>
        if K_eq_dec k k' then
          assoc_del l' k
        else
          (k', v') :: (assoc_del l' k)
    end.

  Lemma get_set_same :
    forall k v l,
      assoc (assoc_set l k v) k = Some v.
  Proof.
    induction l; intros; simpl; repeat (break_match; simpl); subst; congruence.
  Qed.

  Lemma get_set_same' :
    forall k k' v l,
      k = k' ->
      assoc (assoc_set l k v) k' = Some v.
  Proof.
    intros. subst. auto using get_set_same.
  Qed.

  Lemma get_set_diff :
    forall k k' v l,
      k <> k' ->
      assoc (assoc_set l k v) k' = assoc l k'.
  Proof.
    induction l; intros; simpl; repeat (break_match; simpl); subst; try congruence; auto.
  Qed.

  Lemma not_in_assoc :
    forall k l,
      ~ In k (map (@fst _ _) l) ->
      assoc l k = None.
  Proof.
    intros.
    induction l.
    - auto.
    - simpl in *. repeat break_match; intuition.
      subst. simpl in *. congruence.
  Qed.

  Lemma get_del_same :
    forall k l,
      assoc (assoc_del l k) k = None.
  Proof.
    induction l; intros; simpl in *.
    - auto.
    - repeat break_match; subst; simpl in *; auto.
      break_if; try congruence.
  Qed.

  Lemma get_del_diff :
    forall k k' l,
      k <> k' ->
      assoc (assoc_del l k') k = assoc l k.
  Proof.
    induction l; intros; simpl in *.
    - auto.
    - repeat (break_match; simpl); subst; try congruence; auto.
  Qed.

  Lemma get_set_diff_default :
    forall (k k' : K) (v : V) l d,
      k <> k' ->
      assoc_default (assoc_set l k v) k' d = assoc_default l k' d.
  Proof.
    unfold assoc_default.
    intros.
    repeat break_match; auto;
    rewrite get_set_diff in * by auto; congruence.
  Qed.

  Lemma get_set_same_default :
    forall (k : K) (v : V) l d,
      assoc_default (assoc_set l k v) k d = v.
  Proof.
    unfold assoc_default.
    intros.
    repeat break_match; auto;
    rewrite get_set_same in *; congruence.
  Qed.
End assoc.

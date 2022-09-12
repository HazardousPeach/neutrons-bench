Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Omega.

Require Import v1.NeutronTactics.
Require Import v1.Util.

Require Import ProofIrrelevance.

Set Default Timeout 5.


Inductive index (n : nat) : Set :=
| Index : forall m, m < n -> index n.
Implicit Arguments Index [n].

Definition index_nat (n : nat) (i : index n) : nat :=
    match i with Index m _ => m end.
Implicit Arguments index_nat [n].

Ltac mk_index m_ := eapply Index with (m := m_); hide; omega.

Fixpoint index_list' n i (acc : list (index n)) {struct i} : i < n -> list (index n) :=
    fun Hlt =>
        let acc' := Index i Hlt :: acc in
        match i as i_ return i_ < n -> list (index n) with
        | 0 => fun _ => acc'
        | S i' => fun Hlt => @index_list' n i' acc' ltac:(hide; omega)
        end Hlt.
Implicit Arguments index_list'.

Definition index_list n : list (index n) :=
    match n as n_ return n = n_ -> _ with
    | 0 => fun _ => []
    | S n' => fun Heq => @index_list' n n' [] ltac:(hide; omega)
    end eq_refl.

Definition index_ext (n m : nat) (Hlt : n < m) (i : index n) : index m :=
    let (i', Hlt') := i in
    @Index m i' ltac:(hide; omega).
Implicit Arguments index_ext [n m].

Definition index_eq_dec n (x y : index n) : { x = y } + { x <> y }.
destruct x, y.
destruct (eq_nat_dec m m0); [ subst | right; congruence ].
replace l0 with l by (eapply proof_irrelevance).
eauto.
Qed.



(* Using a fixpoint makes `multi 3 nat` definitionally equal to `nat * nat * nat` *)

Fixpoint multi' n A : Set :=
    match n with
    | 0 => A
    | S n => (multi' n A * A)%type
    end.

Fixpoint multi'_rep (n : nat) (A : Set) (v : A) {struct n} : multi' n A :=
    match n as n_ return multi' n_ A with
    | 0 => v
    | S n' => (@multi'_rep n' A v, v)
    end.
Implicit Arguments multi'_rep [A].

Fixpoint multi'_get n A (x : multi' n A) (i : index (S n)) {struct n} : A :=
    match n as n_ return multi' n_ A -> index (S n_) -> A with
    (* Only one element in the multi', so return that.  The index is
       guaranteed to be zero, since `m < S 0`. *)
    | 0 => fun x i => x
    (* Multiple elements.  Might need a recursive call. *)
    | S n' => fun x i =>
            (* The type of `x` is (multi n' A * A).  If the index `i` refers to
               the last element in `x`, we can just extract that with `snd`.
               Otherwise, we need to make a recursive call on `fst x`. *)
            let (i', Hlt) := i in
            if eq_nat_dec (S n') i' then
                snd x
            else
                @multi'_get n' A (fst x) ltac:(mk_index i')
    end x i.
Implicit Arguments multi'_get [n A].

Fixpoint multi'_set n A (x : multi' n A) (i : index (S n)) (v : A) {struct n} : multi' n A :=
    match n as n_ return multi' n_ A -> index (S n_) -> multi' n_ A with
    | 0 => fun x i => v
    | S n' => fun x i =>
            let (i', Hlt) := i in
            if eq_nat_dec (S n') i' then
                (fst x, v)
            else
                (@multi'_set n' A (fst x) ltac:(mk_index i') v, snd x)
    end x i.
Implicit Arguments multi'_set [n A].

Fixpoint multi'_to_list' n A (x : multi' n A) (acc : list A) : list A :=
    match n as n_ return multi' n_ A -> list A with
    | 0 => fun x => x :: acc
    | S n' => fun x => multi'_to_list' n' A (fst x) (snd x :: acc)
    end x.

Definition multi'_to_list n A (x : multi' n A) : list A :=
    multi'_to_list' n A x [].
Implicit Arguments multi'_to_list [n A].

Fixpoint index_multi'' n i : i <= n -> multi' i (index (S n)).
intro Hle.
destruct i.
- refine (Index 0 _). hide. omega.
- refine (index_multi'' n i _, Index (S i) _); hide; omega.
Defined.

Definition index_multi' n : multi' n (index (S n)).
eapply index_multi''. hide. omega.
Defined.

Fixpoint multi'_map n (A B : Set) (f : A -> B) (x : multi' n A) : multi' n B :=
    match n as n_ return multi' n_ A -> multi' n_ B with
    | 0 => fun x => f x
    | S n' => fun x => (multi'_map n' A B f (fst x), f (snd x))
    end x.
Implicit Arguments multi'_map [n A B].

Fixpoint multi'_map_opt n (A B : Set) (f : A -> option B) (x : multi' n A) : option (multi' n B) :=
    match n as n_ return multi' n_ A -> option (multi' n_ B) with
    | 0 => fun x => f x
    | S n' => fun x =>
            multi'_map_opt n' A B f (fst x) >>= fun init =>
            f (snd x) >>= fun last =>
            Some (init, last)
    end x.
Implicit Arguments multi'_map_opt [n A B].

Fixpoint multi'_zip n (A B C : Set) (f : A -> B -> C)
        (x : multi' n A) (y : multi' n B) : multi' n C :=
    match n as n_ return multi' n_ A -> multi' n_ B -> multi' n_ C with
    | 0 => fun x y => f x y
    | S n' => fun x y => (multi'_zip n' A B C f (fst x) (fst y), f (snd x) (snd y))
    end x y.
Implicit Arguments multi'_zip [n A B C].

Definition multi'_eq_dec n (A : Set)
    (eq_dec : forall (x y : A), { x = y } + { x <> y })
    (x y : multi' n A) : { x = y } + { x <> y }.
generalize dependent n. induction n; simpl; intros.
- eapply eq_dec.
- destruct x as [x xv], y as [y yv].
  decide equality.
Defined.
Implicit Arguments multi'_eq_dec [n A].


Theorem multi'_rep_get : forall n (A : Set) i (v : A),
    multi'_get (multi'_rep n v) i = v.
induction n; intros.
{ simpl. reflexivity. } (* zero case *)

unfold multi'_rep, multi'_get. fold multi'_rep. fold multi'_get.
destruct i as [i' ?].
destruct (eq_nat_dec (S n) i').
- reflexivity.
- eapply IHn.
Qed.

Theorem multi'_get_eq : forall n A (x : multi' n A) i j,
    index_nat i = index_nat j -> multi'_get x i = multi'_get x j.
induction n; intros0 Heqnat.
{ simpl. reflexivity. }

unfold multi'_get. fold multi'_get.
destruct i as [i' ?].
destruct j as [j' ?].
simpl in Heqnat.
destruct (eq_nat_dec (S n) i'); destruct (eq_nat_dec (S n) j'); try omega.
- reflexivity.
- eapply IHn. simpl. assumption.
Qed.

Theorem multi'_set_get : forall n A (x : multi' n A) i j v,
    index_nat i = index_nat j -> multi'_get (multi'_set x i v) j = v.
induction n; intros0 Heqnat.
{ simpl. reflexivity. }

unfold multi'_get, multi'_set. fold multi'_get. fold multi'_set.
destruct i as [i' ?].
destruct j as [j' ?].
simpl in Heqnat.
destruct (eq_nat_dec (S n) i'); destruct (eq_nat_dec (S n) j'); try omega.
- reflexivity.
- eapply IHn. simpl. assumption.
Qed.

Theorem multi'_set_get_other : forall n A (x : multi' n A) i j v,
    index_nat i <> index_nat j -> multi'_get (multi'_set x i v) j = multi'_get x j.
induction n; intros0 Hneqnat.
{ destruct i. destruct j. simpl in Hneqnat. omega. }

unfold multi'_get, multi'_set. fold multi'_get. fold multi'_set.
destruct i as [i' ?].
destruct j as [j' ?].
simpl in Hneqnat.
destruct (eq_nat_dec (S n) i'); destruct (eq_nat_dec (S n) j'); try omega.
- reflexivity.
- reflexivity.
- eapply IHn. simpl. assumption.
Qed.


Lemma multi'_get_shrink :
    forall n A (x : multi' n A) (v : A) (i1 : index (2 + n)) (i2 : index (1 + n)),
    index_nat i1 = index_nat i2 ->
    multi'_get ((x, v) : multi' (1 + n) A)  i1 = multi'_get x i2.
intros ? ? ? ? ? ? Heq.
compute [plus] in *.
destruct i1 as [ i1' Hlt1 ].
destruct i2 as [ i2' Hlt2 ].
simpl in Heq. subst.

unfold multi'_get. fold multi'_get.
destruct (eq_nat_dec _ _); [ omega | ].
simpl.
eapply multi'_get_eq. simpl. reflexivity.
Qed.

Lemma multi'_get_ext_fst : forall n A (x : multi' n A) (v : A) i Hlt,
    multi'_get ((x, v) : multi' (S n) A) (@index_ext (S n) (2 + n) Hlt i) = multi'_get x i.
intros.
destruct i as [ i' Hlt' ].
rewrite multi'_get_shrink with (i2 := @Index (S n) i' ltac:(hide; omega)); cycle 1.
{ simpl. reflexivity. }
eapply multi'_get_eq.
simpl. reflexivity.
Qed.

Lemma multi'_get_snd : forall n A (x : multi' n A) (v : A) Hlt,
    multi'_get ((x, v) : multi' (1 + n) A) (Index (1 + n) Hlt) = v.
intros.
simpl. destruct (eq_nat_dec _ _).
- reflexivity.
- omega.
Qed.

Lemma multi'_get_set_eq : forall n A (x : multi' n A) i, multi'_set x i (multi'_get x i) = x.
induction n; intros.
{ simpl. reflexivity. }

destruct x.
destruct i as [ i' Hlt ].
unfold multi'_set, multi'_get. destruct (eq_nat_dec (S n) i'); fold multi'_set; fold multi'_get.
- simpl. reflexivity.
- rewrite IHn. simpl. reflexivity.
Qed.

Lemma multi'_to_list'_length : forall n A x acc,
    length (@multi'_to_list' n A x acc) = S n + length acc.
first_induction n; intros; simpl.
{ reflexivity. }
rewrite IHn. simpl. omega.
Qed.

Lemma multi'_to_list_length : forall n A x,
    length (@multi'_to_list n A x) = S n.
intros. unfold multi'_to_list.
replace (S n) with (S n + @length A []) by (simpl; omega).
eapply multi'_to_list'_length.
Qed.

Theorem index_multi''_get : forall n i Hle j,
    index_nat (multi'_get (index_multi'' n i Hle) j) = index_nat j.
first_induction i; intros; destruct j as [j Hj].
- simpl. omega.
- unfold multi'_get. destruct (eq_nat_dec (S i) j); fold multi'_get.
  + simpl. assumption.
  + unfold index_multi'', fst. fold index_multi''.
    rewrite IHi. simpl. reflexivity.
Qed.

Theorem index_multi'_get : forall n i,
    index_nat (multi'_get (index_multi' n) i) = index_nat i.
intros. unfold index_multi'. eapply index_multi''_get.
Qed.

Theorem multi'_map_get : forall n (A B : Set) (f : A -> B) (x : multi' n A) i,
    multi'_get (multi'_map f x) i = f (multi'_get x i).
first_induction n; intros; destruct i as [i Hi].
- destruct i; try omega. simpl. reflexivity.
- destruct x as [x y].
  unfold multi'_get. destruct (eq_nat_dec (S n) i); fold multi'_get.
  + simpl. reflexivity.
  + unfold multi'_map. fold multi'_map. unfold fst, snd.
    eapply IHn.
Qed.

Theorem multi'_map_opt_get : forall n (A B : Set) (f : A -> option B) (x : multi' n A) y i,
    multi'_map_opt f x = Some y ->
    f (multi'_get x i) = Some (multi'_get y i).
first_induction n; intros0 Hmap; destruct i as [i Hi].
- destruct i; try omega. simpl. assumption.
- destruct x as [x_init x_last].
  unfold multi'_get. destruct (eq_nat_dec (S n) i); fold multi'_get.
  + simpl in Hmap. unfold bind_option in Hmap. do 2 (break_match; try discriminate).
    fancy_injr <- Hmap. simpl. assumption.
  + simpl in Hmap. unfold bind_option in Hmap. do 2 (break_match; try discriminate).
    eapply IHn. fancy_injr <- Hmap. simpl. assumption.
Qed.

Theorem multi'_zip_get : forall n (A B C : Set) (f : A -> B -> C)
        (x : multi' n A) (y : multi' n B) i,
    multi'_get (multi'_zip f x y) i = f (multi'_get x i) (multi'_get y i).
first_induction n; intros; destruct i as [i Hi].
- destruct i; try omega. simpl. reflexivity.
- destruct x as [x x'], y as [y y'].
  unfold multi'_get. destruct (eq_nat_dec (S n) i); fold multi'_get.
  + simpl. reflexivity.
  + unfold multi'_zip. fold multi'_zip. unfold fst, snd.
    eapply IHn.
Qed.




Definition multi n A : Set :=
    match n with
    | 0 => unit
    | S n => multi' n A
    end.

Definition multi_rep (n : nat) (A : Set) (v : A) : multi n A :=
    match n as n_ return multi n_ A with
    | 0 => tt
    | S n' => multi'_rep n' v
    end.
Implicit Arguments multi_rep [A].

Definition multi_get n A (x : multi n A) (i : index n) : A :=
    match n as n_ return multi n_ A -> index n_ -> A with
    | 0 => fun x i => @HIDDEN _ ltac:(exfalso; destruct i; omega)
    | S n' => fun x i => multi'_get x i
    end x i.
Implicit Arguments multi_get [n A].

Definition multi_set n A (x : multi n A) (i : index n) (v : A) : multi n A :=
    match n as n_ return multi n_ A -> index n_ -> multi n_ A with
    | 0 => fun x i => @HIDDEN _ ltac:(exfalso; destruct i; omega)
    | S n' => fun x i => multi'_set x i v
    end x i.
Implicit Arguments multi_set [n A].

Definition multi_to_list n A (x : multi n A) : list A :=
    match n as n_ return multi n_ A -> list A with
    | 0 => fun _ => []
    | S n' => fun x => multi'_to_list x
    end x.
Implicit Arguments multi_to_list [n A].

Definition index_multi n : multi n (index n) :=
    match n as n_ return multi n_ (index n_) with
    | 0 => tt
    | S n' => index_multi' n'
    end.

Definition multi_map n (A B : Set) (f : A -> B) (x : multi n A) : multi n B :=
    match n as n_ return multi n_ A -> multi n_ B with
    | 0 => fun _ => tt
    | S n' => fun x => multi'_map f x
    end x.
Implicit Arguments multi_map [n A B].

Definition multi_map_opt n (A B : Set) (f : A -> option B) (x : multi n A) : option (multi n B) :=
    match n as n_ return multi n_ A -> option (multi n_ B) with
    | 0 => fun _ => Some tt
    | S n' => fun x => multi'_map_opt f x
    end x.
Implicit Arguments multi_map_opt [n A B].

Definition multi_zip n (A B C : Set) (f : A -> B -> C)
        (x : multi n A) (y : multi n B) : multi n C :=
    match n as n_ return multi n_ A -> multi n_ B -> multi n_ C with
    | 0 => fun _ _ => tt
    | S n' => fun x y => multi'_zip f x y
    end x y.
Implicit Arguments multi_zip [n A B C].

Definition multi_eq_dec n (A : Set)
    (eq_dec : forall (x y : A), { x = y } + { x <> y })
    (x y : multi n A) : { x = y } + { x <> y }.
destruct n.
- destruct x, y. left. reflexivity.
- simpl in x, y. eapply multi'_eq_dec. auto.
Defined.
Implicit Arguments multi_eq_dec [n A].

Notation "x '!!' i" := (multi_get x i)
    (at level 100, i at next level).


Theorem multi_rep_get : forall n (A : Set) i (v : A),
    multi_get (multi_rep n v) i = v.
destruct n; intros.
{ destruct i. omega. }
eauto using multi'_rep_get.
Qed.

Theorem multi_get_eq : forall n A (x : multi n A) i j,
    index_nat i = index_nat j -> multi_get x i = multi_get x j.
destruct n; intros.
{ destruct i. omega. }
eauto using multi'_get_eq.
Qed.

Theorem multi_set_get : forall n A (x : multi n A) i j v,
    index_nat i = index_nat j -> multi_get (multi_set x i v) j = v.
destruct n; intros.
{ destruct i. omega. }
eauto using multi'_set_get.
Qed.

Theorem multi_set_get_other : forall n A (x : multi n A) i j v,
    index_nat i <> index_nat j -> multi_get (multi_set x i v) j = multi_get x j.
destruct n; intros.
{ destruct i. omega. }
eauto using multi'_set_get_other.
Qed.


Lemma multi_get_shrink :
    forall n A (x : multi (1 + n) A) (v : A) (i1 : index (2 + n)) (i2 : index (1 + n)),
    index_nat i1 = index_nat i2 ->
    multi_get ((x, v) : multi (2 + n) A)  i1 = multi_get x i2.
intros. compute [plus] in *.
unfold multi_get.
eauto using multi'_get_shrink.
Qed.

Lemma multi_get_ext_fst : forall n A (x : multi (1 + n) A) (v : A) i Hlt,
    multi_get ((x, v) : multi (2 + n) A) (@index_ext (1 + n) (2 + n) Hlt i) = multi_get x i.
intros. compute [plus] in *.
unfold multi_get.
eauto using multi'_get_ext_fst.
Qed.

Lemma multi_get_snd : forall n A (x : multi (1 + n) A) (v : A) Hlt,
    multi_get ((x, v) : multi (2 + n) A) (Index (1 + n) Hlt) = v.
intros. compute [plus] in *.
unfold multi_get.
eauto using multi'_get_snd.
Qed.

Lemma multi_get_set_eq : forall n A (x : multi n A) i, multi_set x i (multi_get x i) = x.
destruct n; intros.
{ destruct i. omega. }
intros. unfold multi_get, multi_set. eapply multi'_get_set_eq.
Qed.

Lemma multi_to_list_length : forall n A x,
    length (@multi_to_list n A x) = n.
intros. unfold multi_to_list.
destruct n.
- reflexivity.
- eapply multi'_to_list_length.
Qed.

Theorem index_multi_get : forall n i,
    index_nat (multi_get (index_multi n) i) = index_nat i.
intros. destruct n.
- destruct i. omega.
- unfold index_multi. eapply index_multi'_get.
Qed.

Theorem multi_map_get : forall n (A B : Set) (f : A -> B) (x : multi n A) i,
    multi_get (multi_map f x) i = f (multi_get x i).
intros. destruct n.
- destruct i. omega.
- eapply multi'_map_get.
Qed.

Theorem multi_map_opt_get : forall n (A B : Set) (f : A -> option B) (x : multi n A) y i,
    multi_map_opt f x = Some y ->
    f (multi_get x i) = Some (multi_get y i).
intros. destruct n.
- destruct i. omega.
- eapply multi'_map_opt_get. assumption.
Qed.

Theorem multi_zip_get : forall n (A B C : Set) (f : A -> B -> C)
        (x : multi n A) (y : multi n B) i,
    multi_get (multi_zip f x y) i = f (multi_get x i) (multi_get y i).
intros. destruct n.
- destruct i. omega.
- eapply multi'_zip_get.
Qed.


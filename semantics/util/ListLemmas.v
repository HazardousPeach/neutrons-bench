Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Omega.

Require Import v1.NeutronTactics.
Require Import v1.Multi.
Require Import epics.Types.
Require Import epics.Records.
Require Import epics.Step.
Require Import epics.Opcodes.


(* List lemmas - misc *)

(* TODO: move - copied from Interpret.v *)
Lemma in_map_index_list : forall n A x (f : index n -> A),
    In x (map f (index_list n)) ->
    exists i, x = f i.
intros0 Hin.
rewrite in_map_iff in Hin. break_exists. break_and.
eauto.
Qed.

(* List lemmas - forall*)

Lemma forall_app_1 : forall A P (xs ys : list A),
    (Forall P xs /\ Forall P ys) ->
    Forall P (xs ++ ys).
intros. break_and.
rewrite Forall_forall in *.
intros x Hin. apply in_app_or in Hin. destruct Hin; eauto.
Qed.

Lemma forall_app_2 : forall A P (xs ys : list A),
    Forall P (xs ++ ys) ->
    (Forall P xs /\ Forall P ys).
intros. repeat rewrite Forall_forall in *.
split; eauto using in_or_app.
Qed.

Lemma forall_app : forall A P (xs ys : list A),
    Forall P (xs ++ ys) <->
    (Forall P xs /\ Forall P ys).
intros. constructor; eauto using forall_app_1, forall_app_2.
Qed.

Lemma forall_concat : forall A P (xss : list (list A)),
    Forall (Forall P) xss ->
    Forall P (concat xss).
first_induction xss; intros0 Hfa.
{ simpl. constructor. }
inversion Hfa; subst.
simpl. rewrite forall_app. split; eauto.
Qed.

Lemma forall_tail : forall A P (x : A) xs,
    Forall P (x :: xs) ->
    Forall P xs.
inversion 1. assumption.
Qed.
Hint Resolve forall_tail.

Lemma Forall_map : forall A B (P : B -> Prop) (f : A -> B) xs,
    Forall (fun x => P (f x)) xs <-> Forall P (map f xs).
induction xs; intros; split; inversion 1; subst; simpl in *; eauto.
- constructor; eauto. rewrite <- IHxs. assumption.
- constructor; eauto. rewrite -> IHxs. assumption.
Qed.

(*
Lemma forall_for_each : forall n P f,
    (forall i : index n, Forall P (f i)) ->
    Forall P (for_each f).
intros0 Hf.
unfold for_each. eapply forall_concat. rewrite Forall_forall.
intros p Hin. forward eapply in_map_index_list; eauto.
break_exists. subst. eauto.
Qed.
*)

(* List lemmas - skipn *)

Lemma skipn_all : forall A n (xs : list A),
    n >= length xs ->
    skipn n xs = [].
first_induction xs; intros0 Hge.
{ destruct n; reflexivity. }
destruct n; simpl in *; [ omega | ].
eapply IHxs. omega.
Qed.

Lemma skipn_cons : forall A n (xs : list A) x,
    nth_error xs n = Some x ->
    skipn n xs = x :: skipn (S n) xs.
first_induction n; intros0 Hn.
- destruct xs; simpl in *; congruence.
- destruct xs; simpl in *; try congruence.
  eapply IHn. assumption.
Qed.

Lemma skipn_sub : forall A n (xs : list A) x,
    n < length xs ->
    nth_error xs (length xs - S n) = Some x ->
    skipn (length xs - S n) xs = x :: skipn (length xs - n) xs.
intros0 Hn Hlt.

replace (length xs - n) with (S (length xs - S n)) in * by omega.
eapply skipn_cons. assumption.
Qed.

Lemma skipn_sub' : forall A n (xs : list A),
    n < length xs ->
    exists x,
    nth_error xs (length xs - S n) = Some x /\
    skipn (length xs - S n) xs = x :: skipn (length xs - n) xs.
intros0 Hlt.
assert (Hnth : length xs - S n < length xs) by omega.
rewrite <- (nth_error_Some) in Hnth.
destruct (nth_error _ _) eqn:?; try congruence.
eexists; eauto using skipn_sub.
Qed.

(* List lemmas - in *)

Lemma in_concat : forall A (x : A) xss,
    In x (concat xss) ->
    exists xs, In xs xss /\ In x xs.
first_induction xss; intros0 H; simpl in H.
{ destruct H. }
rename a into xs.
eapply in_app_or in H. destruct H as [H | H].
- exists xs. firstorder eauto.
- forward eapply IHxss; eauto. break_exists. break_and.
  firstorder eauto.
Qed.

(*
Lemma in_for_each : forall n f x,
    In x (for_each f) ->
    exists i : index n, In x (f i).
intros0 H.
unfold for_each in H.
eapply in_concat in H. break_exists. break_and.
eapply in_map_index_list in H. break_exists.
subst. eauto.
Qed.
*)

(* Lookup lemmas *)

Lemma lookup_state_type : forall dbs dbt rn rs rt,
    dbt = database_state_type dbs ->
    rt = record_state_type rs ->
    lookup_state dbs rn = Some rs ->
    lookup_type dbt rn = Some rt.
first_induction rn; intros0 Heqdbt Heqrt Hnrs;
destruct dbs; simpl in *; try congruence.
- subst. simpl. congruence.
- subst. simpl in *. eauto.
Qed.

Lemma lookup_config_type : forall dbc dbt rn rc rt,
    dbt = database_config_type dbc ->
    rt = record_config_type rc ->
    lookup_config dbc rn = Some rc ->
    lookup_type dbt rn = Some rt.
first_induction rn; intros0 Heqdbt Heqrt Hnrc;
destruct dbc; simpl in *; try congruence.
- subst. simpl. congruence.
- subst. simpl in *. eauto.
Qed.

Lemma lookup_program_type : forall dbp dbt rn rp rt,
    dbt = database_program_type dbp ->
    rt = record_program_type rp ->
    lookup_program dbp rn = Some rp ->
    lookup_type dbt rn = Some rt.
first_induction rn; intros0 Heqdbt Heqrt Hnrc;
destruct dbp; simpl in *; try congruence.
- subst. simpl. congruence.
- subst. simpl in *. eauto.
Qed.

Lemma lookup_config_type_ex : forall dbc dbt rn rc,
    dbt = database_config_type dbc ->
    lookup_config dbc rn = Some rc ->
    exists rt, lookup_type dbt rn = Some rt.
first_induction rn; intros0 Heqdbt Hnrc;
destruct dbt; destruct dbc; simpl in *; try congruence.
- eexists. reflexivity.
- fancy_injection Heqdbt. eapply IHrn; eauto.
Qed.

Lemma lookup_state_type_eq : forall dbs dbt rn rs rt,
    dbt = database_state_type dbs ->
    lookup_state dbs rn = Some rs ->
    lookup_type dbt rn = Some rt ->
    rt = record_state_type rs.
first_induction rn; intros0 Heqdbt Hls Hlt;
subst dbt; destruct dbs; simpl in *; try congruence.
eapply IHrn; eauto.
Qed.


Lemma lookup_Some_lt : forall A xs idx x,
    @lookup A xs idx = Some x ->
    idx < length xs.
intros. unfold lookup in *. rewrite <- nth_error_Some. congruence.
Qed.

Lemma lookup_lt_Some_ex : forall A xs idx,
    idx < length xs ->
    exists x, @lookup A xs idx = Some x.
intros. unfold lookup in *. rewrite <- nth_error_Some in H.
destruct (nth_error xs idx).
- eexists. reflexivity.
- congruence.
Qed.

Lemma lookup_length_ex : forall A B xs ys idx x,
    @lookup A xs idx = Some x ->
    (* Put length premise second so it gets processed later by `; eauto`. *)
    length xs = length ys ->
    exists y, @lookup B ys idx = Some y.
first_induction idx; intros;
destruct xs; simpl in *; try congruence;
destruct ys; simpl in *; try congruence.
- eexists. reflexivity.
- eapply IHidx; eauto.
Qed.

Lemma lookup_map : forall A B f xs rn x,
    @lookup A xs rn = Some x ->
    @lookup B (map f xs) rn = Some (f x).
first_induction rn; intros0 Hlook; destruct xs; simpl in *; try congruence.
eapply IHrn. assumption.
Qed.

Lemma lookup_map' : forall A B f xs ys rn x,
    @lookup A xs rn = Some x ->
    ys = map f xs ->
    @lookup B ys rn = Some (f x).
intros0 Hlook Heq. subst ys. eauto using lookup_map.
Qed.



Lemma sum_lt_init : forall xs x x',
    x < x' ->
    fold_left Nat.add xs x < fold_left Nat.add xs x'.
first_induction xs; intros0 Hlt; simpl in *.
{ assumption. }
apply IHxs. omega.
Qed.

Lemma sum_base_split : forall b1 b2 xs,
    fold_left Nat.add xs (b1 + b2) = b1 + fold_left Nat.add xs b2.
first_induction xs; intros; simpl.
{ omega. }
replace (b1 + b2 + a) with (b1 + (b2 + a)) by omega.
eapply IHxs.
Qed.

Lemma sum_base_add : forall b xs,
    fold_left Nat.add xs b = b + fold_left Nat.add xs 0.
intros.
replace b with (b + 0) at 1 by omega.
eapply sum_base_split.
Qed.

Lemma sum_cons : forall x xs base,
    fold_left Nat.add (x :: xs) base =
    x + fold_left Nat.add xs base.
intros. simpl.
rewrite Nat.add_comm.
eapply sum_base_split.
Qed.

Lemma sum_app : forall xs1 xs2 base,
    fold_left Nat.add (xs1 ++ xs2) base =
    base + fold_left Nat.add xs1 0 + fold_left Nat.add xs2 0.
intros.
rewrite fold_left_app. simpl.
rewrite <- sum_base_add, <- sum_base_add.
reflexivity.
Qed.

Lemma sum_init' : forall xs base x,
    fold_left Nat.add xs (base + x) =
    base + fold_left Nat.add xs x.
first_induction xs; intros; simpl.
{ omega. }
replace (base + x + a) with (base + (x + a)) by omega.
apply IHxs.
Qed.

Lemma sum_init : forall xs base,
    fold_left Nat.add xs base =
    base + fold_left Nat.add xs 0.
intros. replace (base) with (base + 0) at 1 by omega. eapply sum_init'.
Qed.




(* list_magic and friends *)

(* core lemmas used by list_magic *)
Lemma Forall_nth_error : forall X (P : X -> Prop) xs,
    Forall P xs ->
    (forall i x, nth_error xs i = Some x -> P x).
intros.
rewrite Forall_forall in *.
eauto using nth_error_In.
Qed.

Lemma nth_error_Forall : forall X (P : X -> Prop) xs,
    (forall i x, nth_error xs i = Some x -> P x) ->
    Forall P xs.
intros. rewrite Forall_forall in *. intros.
forward eapply In_nth_error; eauto. break_exists. eauto.
Qed.

Lemma Forall2_length : forall X Y (P : X -> Y -> Prop) xs ys,
    Forall2 P xs ys ->
    length xs = length ys.
induction xs; intros0 Hfa; invc Hfa; simpl; eauto.
Qed.

Lemma Forall2_nth_error : forall X Y (P : X -> Y -> Prop) xs ys,
    Forall2 P xs ys ->
    (forall i x y,
        nth_error xs i = Some x ->
        nth_error ys i = Some y ->
        P x y).
induction xs; intros0 Hfa; invc Hfa; intros0 Hnx Hny.
- destruct i; discriminate Hnx.
- destruct i; simpl in Hnx, Hny.
  + congruence.
  + eapply IHxs; eauto.
Qed.

Lemma nth_error_Forall2 : forall X Y (P : X -> Y -> Prop) xs ys,
    length xs = length ys ->
    (forall i x y,
        nth_error xs i = Some x ->
        nth_error ys i = Some y ->
        P x y) ->
    Forall2 P xs ys.
induction xs; intros0 Hlen Hnth; destruct ys; invc Hlen.
- constructor.
- constructor.
  + eapply Hnth with (i := 0); reflexivity.
  + eapply IHxs; eauto.
    intros. eapply Hnth with (i := S i); simpl; eauto.
Qed.

Lemma length_nth_error_Some : forall X Y  xs ys x i,
    @length X xs = @length Y ys ->
    nth_error xs i = Some x ->
    exists y, nth_error ys i = Some y.
intros.
destruct (nth_error ys i) eqn:?; try eauto.
rewrite nth_error_None in *.
assert (nth_error xs i <> None) by congruence.
rewrite nth_error_Some in *.
omega.
Qed.

Lemma Forall2_nth_error_Some : forall X Y (P : X -> Y -> Prop) xs ys x i,
    Forall2 P xs ys ->
    nth_error xs i = Some x ->
    exists y, nth_error ys i = Some y.
intros. eapply length_nth_error_Some. eapply Forall2_length. all:eauto.
Qed.


(* list_magic_using H:
   
   Given this context and goal:

    H : forall i,
        forall x, nth_error xs i = Some x ->
        forall y, nth_error ys i = Some y ->
        P x ->
        Q y ->
        R x y ->
        S x
    Hp : Forall P xs
    Hq : Forall Q ys
    Hr : Forall2 R xs ys
     -----
    Forall S x

   Complete the entire proof, by combining `H` with the lemmas above.
 *)

Ltac collect_length_hyps :=
    repeat match goal with
    | [ H : Forall2 _ ?xs_ ?ys_ |- _ ] =>
            lazymatch goal with
            | [ H : length xs_ = length ys_ |- _ ] => fail (* already known *)
            | [ |- _ ] => 
                    forward eapply Forall2_length with (xs := xs_) (ys := ys_) (1 := H)
            end
    end.

Ltac find_matching_entries HH i :=
    repeat match type of HH with
    | forall y, nth_error ?ys_ i = Some y -> _ =>
            first
                [ specialize (HH ?? **)
                | let Hexist := fresh "H" in
                  let y := fresh "y" in
                  let Hy := fresh "H" y in
                  forward eapply length_nth_error_Some with (ys := ys_) as Hexist;
                  [ | eassumption | ];
                  [ congruence | ];
                  destruct Hexist as [y Hy];
                  specialize (HH y Hy) ]
    end.

Ltac require_no_match P :=
    lazymatch goal with
    | [ H : P |- _ ] => fail "expected no hypothesis matching" P ", but found" H
    | [ |- _ ] => idtac
    end.

Ltac collect_entry_hyps i :=
    repeat match goal with
    | [ Hfa : Forall ?P ?xs, Hnth : nth_error ?xs i = Some ?x |- _ ] =>
            require_no_match (P x);
            assert (P x) by (eapply Forall_nth_error with (1 := Hfa) (2 := Hnth))
    | [ Hfa : Forall2 ?P ?xs ?ys,
        Hnx : nth_error ?xs i = Some ?x,
        Hny : nth_error ?ys i = Some ?y |- _ ] =>
            require_no_match (P x y);
            assert (P x y) by
                (eapply Forall2_nth_error with (1 := Hfa) (2 := Hnx) (3 := Hny))
    end.

Ltac list_magic_using HH :=
    let i := fresh "i" in
    collect_length_hyps;
    (eapply nth_error_Forall || (eapply nth_error_Forall2; [congruence | ..]));
    intro i; intros;
    specialize (HH i);
    collect_length_hyps; find_matching_entries HH i; collect_entry_hyps i;
    eapply HH; eauto.


(* list_magic_on (xs, (ys, (zs, tt))):

   Assert and attempt to prove a suitable `H`, based on the uses of `Forall` on
   `xs`, `ys`, and `zs` in the context and goal.  Solves goals of the form
   `Forall P xs` or `Forall P xs ys`, but may produce a subgoal to prove that
   `P` holds on a particular `x`. *)

Ltac build_list_magic_hyp_type_inner lists G :=
    let i := fresh "i" in
    simple refine (forall i : nat, (_ : Prop));
    let rec loop ls :=
        lazymatch ls with
        | (?l, ?ls) =>
                let x := fresh l "_" i in
                let Hx := fresh "H" x in
                simple refine (forall x, forall Hx : nth_error l i = Some x, (_ : Prop));
                loop ls
        | tt => idtac
        end in
    loop lists;
    repeat match goal with
    | [ Hfa : Forall ?P ?xs,
        Hnth : nth_error ?xs i = Some ?x |- _ ] =>
            simple refine (P x -> (_ : Prop));
            clear Hfa
    | [ Hfa : Forall2 ?P ?xs ?ys,
        Hnthx : nth_error ?xs i = Some ?x,
        Hnthy : nth_error ?ys i = Some ?y |- _ ] =>
            simple refine (P x y -> (_ : Prop));
            clear Hfa
    end;
    lazymatch G with
    | Forall ?P ?xs =>
            lazymatch goal with
            | [ Hnth : nth_error xs i = Some ?x |- _ ] =>
                    exact (P x)
            end
    | Forall2 ?P ?xs ?ys =>
            lazymatch goal with
            | [ Hnthx : nth_error xs i = Some ?x,
                Hnthy : nth_error ys i = Some ?y |- _ ] =>
                    exact (P x y)
            end
    end.

Ltac build_list_magic_hyp_type H_ty lists :=
    match goal with
    | [ |- ?G ] =>
            simple refine (let H_ty : Prop := _ in _);
            [ build_list_magic_hyp_type_inner lists G
            | simpl in H_ty ]
    end.

Ltac list_magic_on lists :=
    let H := fresh "H" in
    let H_ty := fresh H "_ty" in
    build_list_magic_hyp_type H_ty lists;
    assert (H : H_ty); unfold H_ty in *; clear H_ty;
        [ intros; eauto | try list_magic_using H ].



Fixpoint numbered' {A} n (xs : list A) :=
    match xs with
    | [] => []
    | x :: xs => (n, x) :: numbered' (S n) xs
    end.

Definition numbered {A} (xs : list A) := numbered' 0 xs.

Lemma numbered'_map_snd : forall A n (xs : list A),
    map snd (numbered' n xs) = xs.
first_induction xs; intros; eauto.
- simpl. f_equal. eauto.
Qed.

Lemma numbered_map_snd : forall A (xs : list A),
    map snd (numbered xs) = xs.
unfold numbered. intros. eapply numbered'_map_snd.
Qed.


Definition map_partial {A B} (f : A -> option B) : list A -> option (list B) :=
    let fix go xs :=
        match xs with
        | [] => Some []
        | x :: xs =>
                match f x, go xs with
                | Some y, Some ys => Some (y :: ys)
                | _, _ => None
                end
        end in go.

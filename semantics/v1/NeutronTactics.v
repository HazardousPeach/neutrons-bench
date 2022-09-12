Require Import List.
Import ListNotations.


Ltac subst_max :=
  repeat match goal with
           | [ H : ?X = _ |- _ ]  => subst X
           | [H : _ = ?X |- _] => subst X
         end.

Ltac inv H := inversion H; subst_max.
Ltac invc H := inv H; clear H.
Ltac invcs H := invc H; simpl in *.

Ltac break_if :=
  match goal with
    | [ |- context [ if ?X then _ else _ ] ] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
    | [ H : context [ if ?X then _ else _ ] |- _] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

Ltac break_match :=
  match goal with
    | [ |- context [ match ?X with _ => _ end ] ] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
    | [ H : context [ match ?X with _ => _ end ] |- _] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

Ltac break_exists :=
  repeat match goal with
           | [H : exists _, _ |- _ ] => destruct H
         end.

Ltac break_and :=
  repeat match goal with
           | [H : _ /\ _ |- _ ] => destruct H
         end.

Ltac solve_by_inversion' tac :=
  match goal with
    | [H : _ |- _] => solve [inv H; tac]
  end.

Ltac solve_by_inversion := solve_by_inversion' auto.

Ltac apply_fun f H:=
  match type of H with
    | ?X = ?Y => assert (f X = f Y)
  end.

Ltac conclude H tac :=
  (let H' := fresh in
   match type of H with
     | ?P -> _ => assert P as H' by (tac)
   end; specialize (H H'); clear H').

Ltac concludes :=
  match goal with
    | [ H : ?P -> _ |- _ ] => conclude H auto
  end.

Ltac forward_ H :=
  let H' := fresh in
   match type of H with
     | ?P -> _ => assert P as H'
   end.

Ltac forwards :=
  match goal with
    | [ H : ?P -> _ |- _ ] => forward_ H
  end.

Ltac find_contradiction :=
  match goal with
    | [ H : ?X = _, H' : ?X = _ |- _ ] => rewrite H in H'; solve_by_inversion
  end.

Ltac find_rewrite :=
  match goal with
    | [ H : ?X _ _ _ _ = _, H' : ?X _ _ _ _ = _ |- _ ] => rewrite H in H'
    | [ H : ?X = _, H' : ?X = _ |- _ ] => rewrite H in H'
    | [ H : ?X = _, H' : context [ ?X ] |- _ ] => rewrite H in H'
    | [ H : ?X = _ |- context [ ?X ] ] => rewrite H
  end.

Ltac find_inversion :=
  match goal with
    | [ H : ?X _ _ _ _ = ?X _ _ _ _ |- _ ] => invc H
    | [ H : ?X _ _ _ = ?X _ _ _ |- _ ] => invc H
    | [ H : ?X _ _ = ?X _ _ |- _ ] => invc H
    | [ H : ?X _ = ?X _ |- _ ] => invc H
  end.

Require Import Arith.
Ltac do_bool :=
  repeat match goal with
    | [ H : beq_nat _ _ = true |- _ ] => apply beq_nat_true in H
    | [ H : beq_nat _ _ = false |- _ ] => apply beq_nat_false in H
    | [ H : andb _ _ = true |- _ ] => apply Bool.andb_true_iff in H
    | [ H : negb _ = true |- _ ] => apply Bool.negb_true_iff in H
    | [ |- context [ andb _ _ ] ] => apply Bool.andb_true_iff
    | [ |- context [ leb _ _ ] ] => apply leb_correct
    | [ |- context [ _ <> false ] ] => apply Bool.not_false_iff_true
    | [ |- beq_nat _ _ = false ] => apply beq_nat_false_iff
  end.

Ltac clear_refl :=
    repeat match goal with
    | [ H : ?x = ?x |- _ ] => clear H
    end.


(* Hypothesis matching tactics *)

Tactic Notation "with" constr(ctor) "," tactic3(tac) :=
    match goal with
    | [ H : ctor |- _ ] => tac H
    end.

Tactic Notation "with" constr(ctor) "hyp" "," tactic3(tac) :=
    match goal with
    | [ H : context [ ctor ] |- _ ] => tac H
    end.

Tactic Notation "with" "pair" "of" constr(T) "," tactic3(tac) :=
    match goal with
    | [ x1 : T, x2 : T |- _ ] => tac T x1 x2
    end.

Tactic Notation "with" "each" "pair" "," tactic3(tac) :=
    repeat match goal with
    | [ x1 : ?T, x2 : ?T |- _ ] => tac T x1 x2
    end.


Ltac eta_destruct := fun H => destruct H.

Ltac eta_inversion := fun H => inversion H.


(* Explicit unification *)

(* Unify two types, such as `x = Some ?z` and `x = Some y`.  This will
   instantiate existentials but otherwise has no effect on the context. *)
Tactic Notation "unify" uconstr(x) "with" uconstr(y) :=
    let Htmp := fresh "Htmp" in
    refine (let Htmp : False -> x := fun false : False =>
        match false return y with end
    in _);
    clear Htmp.

Tactic Notation "unify" "type" "of" constr(H) "with" uconstr(y) :=
    let T := type of H in
    unify T with y.

Tactic Notation "unify" uconstr(x) "with" "type" "of" constr(H) :=
    let T := type of H in
    unify x with T.

Tactic Notation "unify" "type" "of" constr(H1) "with" "type" "of" constr(H2) :=
    let T1 := type of H1 in
    let T2 := type of H2 in
    unify T1 with T2.

(* Better hypothesis matching tactics *)

(* Match a hypothesis that unifies with the pattern.  The pattern may contain
   underscores, as in `refine`. *)
Tactic Notation "on" uconstr(pat) "," tactic3(tac) :=
    let Htmp := fresh "Htmp" in
    match goal with
    | [ H : _ |- _ ] =>
            unify type of H with pat;
            tac H
    | _ => fail 1 "found no hypothesis matching pattern" pat
    end.

(* Match a hypothesis that contains the pattern.  The pattern must be a
   complete term (no underscores). *)
Tactic Notation "on" "~" constr(pat) "," tactic3(tac) :=
    match goal with
    | [ H : context [ pat ] |- _ ] => tac H
    | _ => fail 1 "found no hypothesis matching pattern ~" pat
    end.

Tactic Notation "on" ">" constr(pat) "," tactic3(tac) :=
    match goal with
    | [ H : ?T |- _ ] =>
            let rec go x :=
                match x with
                | pat => tac H
                | ?x' _ => go x'
                | _ => fail 1
                end
            in go T
    | _ => fail 1 "found no hypothesis matching pattern >" pat
    end.

(* Eta-expanded versions of some tactics, for use with `on`. *)
Ltac destruct_ := fun H => destruct H.
Ltac discriminate_ := fun H => discriminate H.
Ltac inversion_ := fun H => inversion H.
Ltac idtac_ := fun H => idtac H.
Ltac contradict_ := fun H => contradict H.
Ltac try_ tac := fun H => try (tac H).




Tactic Notation "require" "no" "hypothesis" constr(prop) :=
    match goal with
    | [ H : prop |- _ ] => fail 1 "hypothesis already exists:" prop
    | [ |- _ ] => idtac
    end.

Tactic Notation "assert" "fresh" constr(prop) "by" tactic3(tac) :=
    require no hypothesis prop;
    assert prop by tac.

Tactic Notation "assert" "fresh" constr(prop) :=
    require no hypothesis prop;
    assert prop.


Ltac equate_and_rewrite tac T x1 x2 :=
    let Heq := fresh "Heq" in
    assert (Heq : x1 = x2) by (tac);
    try rewrite <- Heq in *;
    try clear Heq;
    try clear x2.

Tactic Notation "equate" "in" "type" constr(T) "by" tactic3(tac) :=
    with pair of T, equate_and_rewrite tac.

(* "equate in type T": Find two values `x1, x2 : T` in the context for which we
 * can prove `x1 = x2`.  Then use `x1 = x2` to rewrite all instances of `x2` to
 * `x1`. *)
Tactic Notation "equate" "in" "type" constr(T) :=
    equate in type T by eauto.

Tactic Notation "equate" "in" "type" constr(T) "using" constr(lemma) :=
    equate in type T by (eauto using lemma).

Tactic Notation "equate" "in" "type" constr(T) "using" constr(lemma1) "," constr(lemma2) :=
    equate in type T by (eauto using lemma1, lemma2).

Tactic Notation "clear" "duplicates" :=
    repeat match goal with
    | [ H1 : ?P, H2 : ?P |- _ ] =>
            match type of P with
            | Prop => clear H2
            end
    end.

Tactic Notation "equate" "all" "by" tactic3(tac) :=
    with each pair, equate_and_rewrite tac.

Tactic Notation "equate" "all" :=
    equate all by eauto.


(* Forward reasoning with a tactic.

   Suppose you want to establish an intermediate hypothesis using a specific
   lemma.  Normally you must either specify either the type of the hypothesis
   (when using `assert`) or the number of arguments for the lemma (when using
   `refine (let x := f a b c in _)`.  With `forward`, you specify neither:
   `forward eapply some_lemma` will introduce a hypothesis whose type is the
   conclusion of `some_lemma` (with arguments filled in with existential
   variables).

   Other tactics can be used in placed of `eapply`.  The tactic `forward tac`
   introduces a new hypothesis whose type is an existential variable, then
   applies `tac` to prove that hypothesis.  For this to work, `tac` must be
   able to do some amount of forward reasoning - in other words, `tac` must do
   something useful even when the type of the goal is completely unknown.
 *)

(* Most general form of `forward`.  Do forward reasoning with `tac`, then apply
   ltac function `next` to the hypothesis. *)
Tactic Notation "with" "forward" tactic3(tac) "," tactic3(next) :=
    simple refine (let _forward_tmp : _ := _ in _);
    [ shelve
    | tac
    | let H := match goal with | [ H : _ |- _ ] => H end in
      let H' := fresh "H" in
      rename H into H';
      clearbody H';
      next H'
    ].

Tactic Notation "forward" tactic3(tac) :=
    with forward tac, fun _ => idtac.

(* Perform forward reasoning with `tac`, and call the introduced hypothesis
   `name`. *)
Tactic Notation "forward" tactic3(tac) "as" ident(name) :=
    with forward tac, fun tmp => rename tmp into name.

(* Perform forward reasoning with `tac`, then destruct the introduced
   hypothesis and name the pieces `names`.  This form does not support the full
   generality of `destruct` (specifically, it doesn't handle multiple
   contstructors and nested patterns).  If you need more flexibility, use
   something like `with forward tac, fun H => destruct H as [ a [ b c ] ]`.
 *)
Tactic Notation "forward" tactic3(tac) "as" "[" ne_ident_list(names) "]" :=
    with forward tac, fun tmp => destruct tmp as [ names ].



(* `inversion ... using` variants of `inv` *)

Ltac inv_using I H := inversion H using I; intros; subst_max.
Ltac invc_using I H := inv_using I H; clear H.
Ltac invcs_using I H := invc_using I H; simpl in *.


(* Wrappers for various tactics, for use with `on` *)

Ltac apply_ H := apply H.
Ltac eapply_ H := eapply H.

Ltac apply_lem lem H := apply lem in H.
Ltac eapply_lem lem H := eapply lem in H.


Ltac rewrite_fwd lem H := rewrite -> lem in H.
Ltac rewrite_rev lem H := rewrite <- lem in H.



(* Construct an existential witness using tactics. *)
Ltac assert_exists :=
    let go x T :=
            let x' := fresh x in
            assert (x' : T);
            [ | exists x' ] in
    match goal with
    | [ |- exists (x : ?T), _ ] => go x T
    | [ |- { x : ?T | _ } ] => go x T
    end.


(* Change the current goal to an equivalent one in which argument "x" is the
 * first one. *)
Tactic Notation "make_first" ident(x) :=
    try intros until x;
    move x at top;
    repeat match goal with
    | [ y : _ |- _ ] => generalize y; clear y
    end.

(* Move "x" to the front of the goal, then perform induction. *)
Ltac first_induction x := make_first x; induction x.



(* Introduce dependent premises under automatic names, then introduce remaining
   (dependent) premises under the given names.  This lets you name only the
   "prop-like" premises, such as `intros0 Hx Hy` to introduce x, y, and two
   named hypotheses about x and y.
*)
Tactic Notation "intros0" ne_ident_list(xs) :=
    intros until 0; intros xs.



(* `sink_in`: Take the topmost `forall` in the type of a hypothesis, and move
   it as late as possible (basically, move it just before the first premise
   that actually depends on it).

   For example:
     H : forall x y, P y -> P x -> Q x y
   becomes:
     H : forall y, P y -> forall x, P x -> Q x y
 *)

(* Helper for computing the new type of the hypothesis *)
Ltac sink_ty T :=
    lazymatch T with
    | fun (v : ?Vars) => forall (x : ?U), @?V v -> @?body v x =>
            let subterm := constr:(fun (v' : Vars) =>
                    forall (x : U), body v' x) in
            let subterm := eval cbv beta in subterm in
            let rest := sink_ty subterm in
            let result := constr:(fun (v : Vars) => V v -> rest v) in
            (* let result := eval cbv beta iota delta [projT1 projT2] in result in *)
            result
    | fun (v : ?Vars) => forall (x : ?U), forall (y : @?V v), @?body v x y =>
            let subterm := constr:(fun (v' : {v : Vars & V v}) =>
                    forall (x : U), body (projT1 v') x (projT2 v')) in
            let subterm := eval cbv beta in subterm in
            let rest := sink_ty subterm in
            let result := constr:(fun (v : Vars) => forall (y : V v), rest (@existT Vars V v y)) in
            let result := eval cbv beta iota delta [projT1 projT2] in result in
            result
    | fun _ => _ => constr:(T)
    end.

(* Compute the new type obtained by moving the topmost `forall` in `T`. *)
Ltac sink_ty' T :=
    let sunk := sink_ty (fun (x : unit) => T) in
    let sunk := constr:(sunk tt) in
    let sunk := eval cbv beta in sunk in
    constr:sunk.

(* Take the topmost `forall` in H, and push it down past as many `forall` and `->`
   as possible. *)
Ltac sink_in H :=
    let H' := fresh H in
    rename H into H';
    let T' := type of H' in
    let T := sink_ty' T' in
    assert (H : T) by eauto;
    clear H'.



(* `set_inversion`: A limited form of `inversion` that works in `Set` contexts. *)

Set Implicit Arguments.
Inductive marker (T : Type) (A : T) := Marker : marker A.
Unset Implicit Arguments.

Ltac set_inversion H :=
  let P := fresh "P" in
  evar (P : Prop);
  assert (P);
  [ unfold P; assert (marker 0) by constructor;
    inversion H;
    let rec loop :=
        lazymatch goal with
        | [ H : ?T |- _ ] =>
                lazymatch T with
                | marker 0 => instantiate (1 := True); constructor; clear H
                | _ = _ => rewrite <- H in *; clear H; loop
                | _ => first
                        [ instantiate (1 := _ /\ _);
                          split; [ exact H | ]
                        | idtac "warning: unusable dependent hypothesis: " T
                        ]; clear H; loop
                end
        end
    in loop
  | unfold P in *; clear P; break_and;
    match goal with [ H : True |- _ ] => clear H end].


(* Variants on `specialize` *)

(* Specialize using an assumption from the context. *)
Ltac spec_assume pf :=
    match type of pf with
    | ?T -> _ =>
            match goal with
            | [ H : T |- _ ] => specialize (pf H)
            end
    end.

(* Specialize using `eq_refl`. *)
Ltac spec_eq pf := specialize (pf eq_refl).

(* Specialize using `assert`. *)
Ltac spec_assert pf :=
    match type of pf with
    | ?T -> _ =>
            let H := fresh "H" in
            assert (H : T);
            [ clear pf | specialize (pf H) ]
    end.

Ltac spec_evar pf :=
    match type of pf with
    | forall (x : ?T), _ =>
            let x := fresh x in
            evar (x : T);
            specialize (pf x);
            unfold x in *;
            clear x
    end.

Tactic Notation "spec" ident(pf) "by" tactic3(tac) :=
    match type of pf with
    | forall (x : ?T), _ =>
            let H := fresh "H" in
            assert (H : T);
            [ clear pf; tac | specialize (pf H) ]
    end.


(* Utility tactic for hiding proof terms inside of functions.  This is useful
   for functions that will sometimes need to be unfolded, to keep the giant
   proof term from wasting tons of screen space. *)

Definition HIDDEN (A : Type) (x : A) : A := x.
(* Make all arguments implicit so `@HIDDEN P (giant proof)` prints as `HIDDEN`. *)
Implicit Arguments HIDDEN [A x].

(* The `hide` tactic wraps (with `HIDDEN`) the remainder of the proof of the
   current goal.  Use it like `refine (...); hide; prove stuff...` or
   `$(hide; prove stuff...)$`. *)
Ltac hide := apply @HIDDEN.



(* Dump the entire context and the current goal using `idtac`.  This is useful
   for inspecting the proof state inside `$(...)$`. *)
   
Ltac dump_ctx :=
    match goal with
    | [ H : ?T |- _ ] => idtac H ":" T; fail
    end ||
    match goal with
    | [ |- ?G ] => idtac " --- Goal: " G
    end.


(* Like `fold` but works harder *)
Ltac fold_harder x :=
    let x' := eval compute in x in
    replace x' with x in * by reflexivity.


(* fancy_injection tactic & supporting lemmas *)

(* The `fancy_injection` tactic is a greatly improved version of built-in 
   `injection`.  Running `fancy_injection1 H` is like `injection H; intros`,
   but it can also handle non-constructor injective functions (using a hint
   database).  By calling `fancy_injection_core` directly, it's also possible
   to customize the solver to provide special handling for particular functions.

   There are several variants of `fancy_injection`:

   - `fancy_injection` (without the `1` suffix) works recursively, applying
     itself to all generated equalities.  This lets it handle 3+-ary tuples,
     lists with multiple known elements (as in `a :: b :: c :: xs`), and so on.

   - `fancy_injr1` performs injection, then rewrites the context and goal using
     the generated hypotheses (and clears them).

   - `fancy_injr` is the recursive version of `fancy_injr1`.  The typical
     effect of `fancy_injr H` is to rewrite the context and goal using all
     "obvious" equalities that can be derived from H (and then clear H).

   All `fancy_injection` tactics use the `fancy_injection` hint database to
   to handle non-constructor functions.  This database should include lemmas
   of the form `f x y = f x' y' -> x = x'` and `f x y = f x' y' -> y = y'`.
   Lemmas like `f x y = f x' y' -> x = x' /\ y = y'` will not apply correctly.
 *)

Lemma app_inj_length : forall A (xs1 xs2 ys1 ys2 : list A),
    length xs1 = length ys1 ->
    xs1 ++ xs2 = ys1 ++ ys2 ->
    xs1 = ys1 /\ xs2 = ys2.
first_induction xs1; intros0 Hlen Heq;
destruct ys1 as [ | b ys1 ]; try discriminate Hlen.
{ (* base case *)eauto. }
assert (a = b) by (injection Heq; eauto). subst b.
forward eapply (IHxs1 xs2 ys1 ys2) as [ Hl1 Hl2 ].
- simpl in Hlen. injection Hlen. eauto.
- simpl in Heq. injection Heq. eauto.
- subst. eauto.
Qed.

Lemma app_inj_length_l : forall A (xs1 xs2 ys1 ys2 : list A),
    length xs1 = length ys1 ->
    xs1 ++ xs2 = ys1 ++ ys2 ->
    xs1 = ys1.
intros. forward eapply app_inj_length as [ Hl Hr ]; eauto.
Qed.

Lemma app_inj_length_r : forall A (xs1 xs2 ys1 ys2 : list A),
    length xs1 = length ys1 ->
    xs1 ++ xs2 = ys1 ++ ys2 ->
    xs2 = ys2.
intros. forward eapply app_inj_length as [ Hl Hr ]; eauto.
Qed.


(* solver: Tries to solve the goal.  Gets arguments `H` (the input hypothesis)
           and `n` (the index of the current subterm in the left/right sides
           of that hypothesis)

   rewriter: Maybe does some rewriting to clean up `H`.  Gets `H` as an argument.

   loop: Called on each new hypothesis, so the calling tactic can do multiple
         levels of injection.
 *)
        
Ltac fancy_injection_core H solver rewriter loop :=
    let go n x y :=
        let Heq := fresh H "_eq0" in
        lazymatch x with | y => fail | _ => idtac end;
        assert (Heq : x = y) by solve [ solver H n ];
        loop Heq in
    lazymatch type of H with
    | ?f ?x1 ?x2 ?x3 ?x4 ?x5 = ?f ?y1 ?y2 ?y3 ?y4 ?y5 =>
            try go 1 x1 y1;
            try go 2 x2 y2;
            try go 3 x3 y3;
            try go 4 x4 y4;
            try go 5 x5 y5
    | ?f ?x1 ?x2 ?x3 ?x4 = ?f ?y1 ?y2 ?y3 ?y4 =>
            try go 1 x1 y1;
            try go 2 x2 y2;
            try go 3 x3 y3;
            try go 4 x4 y4
    | ?f ?x1 ?x2 ?x3 = ?f ?y1 ?y2 ?y3 =>
            try go 1 x1 y1;
            try go 2 x2 y2;
            try go 3 x3 y3
    | ?f ?x1 ?x2 = ?f ?y1 ?y2 =>
            try go 1 x1 y1;
            try go 2 x2 y2
    | ?f ?x1 = ?f ?y1 =>
            try go 1 x1 y1
    | ?f = ?g => idtac
    end;
    rewriter H.

Ltac fancy_injection_solver H n :=
    let T := type of H in
    match type of H with
    | _ ++ _ = _ ++ _ =>
            match n with
            | 2 => eapply app_inj_length_l
            | 3 => eapply app_inj_length_r
            end; try exact H; eauto with fancy_injection
    | _ => eauto with fancy_injection || congruence
    end.

Ltac fancy_injection_trivial_rewriter H :=
    match type of H with
    | ?x = ?x => try clear H
    | _ => idtac
    end.

Ltac fancy_injection_rewriter H :=
    match type of H with
    | ?x = ?x => try clear H
    | ?x = ?y => try rewrite H in *; try clear H
    end.

Ltac fancy_injection_rewriter_rev H :=
    match type of H with
    | ?x = ?x => try clear H
    | ?x = ?y => try rewrite <- H in *; try clear H
    end.

Ltac fancy_injection1 H := fancy_injection_core H
    fancy_injection_solver
    fancy_injection_trivial_rewriter
    ltac:fun _ => idtac.

Ltac fancy_injection H := fancy_injection_core H
    fancy_injection_solver
    fancy_injection_trivial_rewriter
    ltac:fun H => (instantiate; fancy_injection H).


Ltac fancy_injr1_ H := fancy_injection_core H
    fancy_injection_solver
    fancy_injection_rewriter
    ltac:fun _ => idtac.

Ltac fancy_injr1_rev_ H := fancy_injection_core H
    fancy_injection_solver
    fancy_injection_rewriter_rev
    ltac:fun _ => idtac.

Tactic Notation "fancy_injr1" constr(H) := fancy_injr1_ H.
Tactic Notation "fancy_injr1" "->" constr(H) := fancy_injr1_ H.
Tactic Notation "fancy_injr1" "<-" constr(H) := fancy_injr1_rev_ H.


Ltac fancy_injr_ H := fancy_injection_core H
    fancy_injection_solver
    fancy_injection_rewriter
    ltac:fun H => (instantiate; fancy_injr_ H).

Ltac fancy_injr_rev_ H := fancy_injection_core H
    fancy_injection_solver
    fancy_injection_rewriter_rev
    ltac:fun H => (instantiate; fancy_injr_rev_ H).

Tactic Notation "fancy_injr" constr(H) := fancy_injr_ H.
Tactic Notation "fancy_injr" "->" constr(H) := fancy_injr_ H.
Tactic Notation "fancy_injr" "<-" constr(H) := fancy_injr_rev_ H.


(* fun notations *)

Notation "**" := (ltac:(eassumption)) (only parsing).
Notation "***" := (ltac:(eauto)) (only parsing).
Notation "??" := (ltac:(shelve)) (only parsing).


(* Exploit injectivity of constructors *)

Ltac inject_some := repeat on (Some _ = Some _), invc.
Ltac inject_pair := repeat on ((_, _) = (_, _)), invc.



(* Lemma and tactic for working with existT *)

Require Import Eqdep_dec.
Require Import EqdepFacts.

Lemma existT_eq : forall {A} (eq_dec : forall (x y : A), { x = y } + { x <> y })
    (P : A -> Type) x y1 y2,
    existT P x y1 = existT P x y2 ->
    y1 = y2.
intros0 eq_dec. intros0 Heq.
eapply eq_dep_eq_dec; eauto.
eapply eq_sigT_eq_dep. assumption.
Qed.

Ltac fix_existT :=
    let rec go :=
        match goal with
        | [ H : existT ?P ?x _ = existT ?P ?x _ |- _ ] =>
                eapply existT_eq in H;
                [ try go | eauto with eq_dec.. ]
        end in go.

Ltac fix_eq_rect :=
    let rec go :=
        match goal with
        | [ H : context [ eq_rect _ _ _ _ _ ] |- _ ] =>
                rewrite <- eq_rect_eq_dec in H;
                [ try go | eauto with eq_dec.. ]
        | [ |- context [ eq_rect _ _ _ _ _ ] ] =>
                rewrite <- eq_rect_eq_dec;
                [ try go | eauto with eq_dec.. ]
        end in go.

Hint Resolve eq_nat_dec : eq_dec.
Hint Resolve Bool.bool_dec : eq_dec.
Hint Resolve list_eq_dec : eq_dec.

Require Import ZArith.
Hint Resolve Z.eq_dec : eq_dec.



(* `remvar` ("remember as evar") - replaces a chunk of your goal with an evar,
   This may make it easier to apply some lemmas.  After solving the main goal,
   you must also prove that the evar's instantiation is compatible with the
   original value.
 *)

Tactic Notation "remvar" uconstr(u) "as" ident(x) :=
    let x' := fresh x "'" in
    let Heq := fresh "Heq" x in
    remember u as x' eqn:Heq in |- *;
    let T := type of x' in
    evar (x : T);
    let H := fresh "H" in
    assert (H : x' = x); cycle 1;
    unfold x in *; clear x;
    [ rewrite H in Heq |- *; clear H
    | rewrite Heq; clear Heq; clear x' ].


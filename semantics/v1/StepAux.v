Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Omega.

Require Import v1.Util.
Require Import v1.ListLemmas.
Require Import v1.EpicsTypes.
Require Import v1.EpicsRecords.
Require Import v1.Step.
Require Import v1.NeutronTactics.

Set Default Timeout 10.
Set Implicit Arguments.


Definition is_db_op op :=
    match op with
    | MSetConst _ _ => true
    | MCopy _ _ _ _ => true
    | MReadLink _ _ _ _ => true
    | MWriteLink _ _ _ _ => true
    | MCalculate _ _ => true
    | MCalculateStr _ _ _ => true
    | MHavocUpdate => true
    | MHavocWrite _ _ => true
    | _ => false
    end.

Definition is_output_op op :=
    match op with
    | MHwWrite _ _ _ => true
    | MScheduleCallback _ _ => true
    | _ => false
    end.

Definition is_special_op op :=
    match op with
    | MProcess _ => true
    | MCalcCond _ _ _ _ => true
    | MCheckPACT => true
    | MHavocProcess _ => true
    | _ => false
    end.

Definition micro_rect_g (P : micro -> Type) (Pl : list micro -> Type) :
    (forall fn val, P (MSetConst fn val)) ->
    (forall fn_src src_ty fn_dest dest_ty, P (MCopy fn_src src_ty fn_dest dest_ty)) ->
    (forall il il_ty fn f_ty, P (MReadLink il il_ty fn f_ty)) ->
    (forall fn f_ty ol ol_ty, P (MWriteLink fn f_ty ol ol_ty)) ->
    (forall fl, P (MProcess fl)) ->
    (forall expr fn_out, P (MCalculate expr fn_out)) ->
    (forall expr fn_out_dbl fn_out_str, P (MCalculateStr expr fn_out_dbl fn_out_str)) ->
    (forall fn f_ty out_ty, P (MHwWrite fn f_ty out_ty)) ->
    (forall fn_cur fn_prev oopt body,
        Pl body ->
        P (MCalcCond fn_cur fn_prev oopt body)) ->
    (forall delay code,
        Pl code ->
        P (MScheduleCallback delay code)) ->
    (P (MCheckPACT)) ->
    (P (MHavocUpdate)) ->
    (forall ol ol_ty, P (MHavocWrite ol ol_ty)) ->
    (forall fl, P (MHavocProcess fl)) ->
    (Pl []) ->
    (forall op ops,
        P op ->
        Pl ops ->
        Pl (op :: ops)) ->
    (forall op, P op).
intros. generalize op. clear op. fix 1.
simple refine (
    let fix micro_list_rect_g ops : Pl ops :=
        match ops as ops_ return Pl ops_ with
        | [] => _
        | op :: ops =>
                let Hop := micro_rect_g op in
                let Hops := micro_list_rect_g ops in
                _
        end in _
).
{ clear micro_rect_g micro_list_rect_g. assumption. }
{ clearbody Hop Hops. clear micro_rect_g micro_list_rect_g. eauto. }
clearbody micro_list_rect_g. clear micro_rect_g.

destruct op; eauto.
Defined.


Definition micro_list_rect_g (P : micro -> Type) (Pl : list micro -> Type) :
    (forall fn val, P (MSetConst fn val)) ->
    (forall fn_src src_ty fn_dest dest_ty, P (MCopy fn_src src_ty fn_dest dest_ty)) ->
    (forall il il_ty fn f_ty, P (MReadLink il il_ty fn f_ty)) ->
    (forall fn f_ty ol ol_ty, P (MWriteLink fn f_ty ol ol_ty)) ->
    (forall fl, P (MProcess fl)) ->
    (forall expr fn_out, P (MCalculate expr fn_out)) ->
    (forall expr fn_out_dbl fn_out_str, P (MCalculateStr expr fn_out_dbl fn_out_str)) ->
    (forall fn f_ty out_ty, P (MHwWrite fn f_ty out_ty)) ->
    (forall fn_cur fn_prev oopt body,
        Pl body ->
        P (MCalcCond fn_cur fn_prev oopt body)) ->
    (forall delay code,
        Pl code ->
        P (MScheduleCallback delay code)) ->
    (P (MCheckPACT)) ->
    (P (MHavocUpdate)) ->
    (forall ol ol_ty, P (MHavocWrite ol ol_ty)) ->
    (forall fl, P (MHavocProcess fl)) ->
    (Pl []) ->
    (forall op ops,
        P op ->
        Pl ops ->
        Pl (op :: ops)) ->
    (forall ops, Pl ops).
intros. generalize ops. clear ops. fix 1. intros.
simple refine (
    match ops as ops_ return Pl ops_ with
    | [] => _
    | op :: ops =>
            let Hop : P op := _ in
            let Hops : Pl ops := micro_list_rect_g ops in
            _
    end
); try clearbody Hops; clear micro_list_rect_g.
- eassumption.
- eapply micro_rect_g; eassumption.
- eauto.
Defined.

Definition micro_rec' (P : micro -> Set) (Pl : list micro -> Set) :=
    micro_rect_g P Pl.

Definition micro_ind' (P : micro -> Prop) (Pl : list micro -> Prop) :=
    micro_rect_g P Pl.

Definition micro_list_ind' (P : micro -> Prop) (Pl : list micro -> Prop) :=
    micro_list_rect_g P Pl.

Definition micro_ind'' (P : micro -> Prop) :
    (forall fn val, P (MSetConst fn val)) ->
    (forall fn_src src_ty fn_dest dest_ty, P (MCopy fn_src src_ty fn_dest dest_ty)) ->
    (forall il il_ty fn f_ty, P (MReadLink il il_ty fn f_ty)) ->
    (forall fn f_ty ol ol_ty, P (MWriteLink fn f_ty ol ol_ty)) ->
    (forall fl, P (MProcess fl)) ->
    (forall expr fn_out, P (MCalculate expr fn_out)) ->
    (forall expr fn_out_dbl fn_out_str, P (MCalculateStr expr fn_out_dbl fn_out_str)) ->
    (forall fn f_ty out_ty, P (MHwWrite fn f_ty out_ty)) ->
    (forall fn_cur fn_prev oopt body,
        Forall P body ->
        P (MCalcCond fn_cur fn_prev oopt body)) ->
    (forall delay code,
        Forall P code ->
        P (MScheduleCallback delay code)) ->
    (P (MCheckPACT)) ->
    (P (MHavocUpdate)) ->
    (forall ol ol_ty, P (MHavocWrite ol ol_ty)) ->
    (forall fl, P (MHavocProcess fl)) ->
    (forall op, P op).
intros. eapply micro_ind' with (Pl := Forall P); eauto.
Defined.


Definition umicro_rec' (P : umicro -> Type) (Pl : list umicro -> Type) :
    (forall fn val, P (USetConst fn val)) ->
    (forall fn_src fn_dest, P (UCopy fn_src fn_dest)) ->
    (forall il fn, P (UReadLink il fn)) ->
    (forall fn ol, P (UWriteLink fn ol)) ->
    (forall fns ol, P (UWriteLinkTyped fns ol)) ->
    (forall fl, P (UProcess fl)) ->
    (forall expr fn_out, P (UCalculate expr fn_out)) ->
    (forall expr fn_out_dbl fn_out_str, P (UCalculateStr expr fn_out_dbl fn_out_str)) ->
    (forall fn out_ty, P (UHwWrite fn out_ty)) ->
    (forall fn_cur fn_prev oopt body,
        Pl body ->
        P (UCalcCond fn_cur fn_prev oopt body)) ->
    (forall delay code,
        Pl code ->
        P (UScheduleCallback delay code)) ->
    (P (UCheckPACT)) ->
    (P (UHavocUpdate)) ->
    (forall ol, P (UHavocWrite ol)) ->
    (forall fl, P (UHavocProcess fl)) ->
    (Pl []) ->
    (forall op ops,
        P op ->
        Pl ops ->
        Pl (op :: ops)) ->
    (forall op, P op).
intros. generalize op. clear op. fix 1.
simple refine (
    let fix umicro_rec'_list ops : Pl ops :=
        match ops as ops_ return Pl ops_ with
        | [] => _
        | op :: ops =>
                let Hop := umicro_rec' op in
                let Hops := umicro_rec'_list ops in
                _
        end in _
).
{ clear umicro_rec' umicro_rec'_list. assumption. }
{ clearbody Hop Hops. clear umicro_rec' umicro_rec'_list. eauto. }
clearbody umicro_rec'_list. clear umicro_rec'.

destruct op; eauto.
Defined.




Inductive MicroForall (P : micro -> Prop) : micro -> Prop:=
| MfCalcCond : forall fn_cur fn_prev oopt body,
        P (MCalcCond fn_cur fn_prev oopt body) ->
        Forall (MicroForall P) body ->
        MicroForall P (MCalcCond fn_cur fn_prev oopt body)
| MfScheduleCallback : forall delay code,
        P (MScheduleCallback delay code) ->
        Forall (MicroForall P) code ->
        MicroForall P (MScheduleCallback delay code)
| MfOther : forall op,
        match op with
        | MCalcCond _ _ _ _ => False
        | MScheduleCallback _ _ => False
        | _ => True
        end ->
        P op ->
        MicroForall P op.

Lemma forall_one : forall P op,
    MicroForall P op ->
    P op.
inversion 1; auto.
Qed.



Definition type_umicro_list dbt rt :=
    let go := type_umicro dbt rt in
    let fix go_list uops : option (list micro) :=
        match uops with
        | [] => Some []
        | uop :: uops =>
                go uop >>= fun uop' =>
                go_list uops >>= fun uops' =>
                Some (uop' :: uops')
        end in go_list.



Inductive type_error_context :=
| TCtxRecord (rn : record_name)
| TCtxOpcode (uop : umicro)
.

Inductive type_error :=
| TyENoSuchRecord (rn : record_name)
| TyENoTypedField (fns : list (field_type_matcher * field_name)) (ty : field_type)
| TyEInContext (ctx : type_error_context) (e : type_error)
| TyEMultipleErrors (e1 e2 : type_error)
.

Definition type_umicro_checked (dbt : database_type) (rt : record_type) :
    umicro -> unit + type_error.
simple refine (
    let fix go (uop : umicro) : unit + type_error :=
        let fix go_list (uops : list umicro) : unit + type_error :=
            match uops with
            | [] => inl tt
            | uop :: uops =>
                match go uop, go_list uops with
                | inl tt, inl tt => inl tt
                | inr e, inl tt => inr e
                | inl tt, inr e => inr e
                | inr e1, inr e2 => inr (TyEMultipleErrors e1 e2)
                end
            end in
        let ctx := TCtxOpcode uop in
        match uop with
        | USetConst fn val => inl tt
        | UCopy fn_src fn_dest => inl tt
        | UReadLink il fn => _
        | UWriteLink fn ol => _
        | UWriteLinkTyped fns ol => _
        | UProcess fl => inl tt
        | UCalculate expr fn_out => inl tt
        | UCalculateStr expr fn_out_dbl fn_out_str => inl tt
        | UHwWrite fn out_ty => inl tt
        | UCalcCond fn_cur fn_prev oopt body => go_list body
        | UScheduleCallback delay code => go_list code
        | UCheckPACT => inl tt
        | UHavocUpdate => inl tt
        | UHavocWrite ol => _
        | UHavocProcess fl => inl tt
        end in go
); try clearbody go; try clearbody go_list.

- (* ReadLink *)
  destruct (lookup_type dbt (fl_rn il)); [ | right; exact (TyENoSuchRecord (fl_rn il)) ].
  exact (inl tt).

- (* WriteLink *)
  destruct (lookup_type dbt (fl_rn ol)); [ | right; exact (TyENoSuchRecord (fl_rn ol)) ].
  exact (inl tt).

- (* WriteLinkTyped *)
  destruct (lookup_type dbt (fl_rn ol)) as [ol_rt | ];
          [ | right; exact (TyENoSuchRecord (fl_rn ol)) ].
  set (ty := record_field_type ol_rt (fl_fn ol)).
  destruct (find_match_for_type fns ty);
        [ | right; exact (TyENoTypedField fns ty) ].
  exact (inl tt).

- (* HavocWrite *)
  destruct (lookup_type dbt (fl_rn ol)); [ | right; exact (TyENoSuchRecord (fl_rn ol)) ].
  exact (inl tt).
Defined.

Definition map_checked {A} (f : A -> unit + type_error) : list A -> unit + type_error.
simple refine (
    let go := f in
    let fix go_list (xs : list A) : unit + type_error :=
        match xs with
        | [] => inl tt
        | x :: xs =>
                match go x, go_list xs with
                | inl tt, inl tt => inl tt
                | inr e, inl tt => inr e
                | inl tt, inr e => inr e
                | inr e1, inr e2 => inr (TyEMultipleErrors e1 e2)
                end
        end in go_list
).
Defined.

Definition type_record_uprogram_checked dbt urp : unit + type_error :=
    map_checked (type_umicro_checked dbt (ru_type urp)) (ru_code urp).

Definition check_numbered_record {A} (f : A -> unit + type_error) (nx : nat * A) :
        unit + type_error :=
    let '(n, x) := nx in
    match f x with
    | inl tt => inl tt
    | inr err => inr (TyEInContext (TCtxRecord n) err)
    end.

Definition type_database_program'_checked dbt udp :=
    map_checked (check_numbered_record (type_record_uprogram_checked dbt)) (numbered udp).

Definition type_database_program_checked udp :=
    type_database_program'_checked (map ru_type udp) udp.


Inductive results_match {A : Type} :
    (option A) ->
    (unit + type_error) ->
    Prop :=
| RmYes : forall x, results_match (Some x) (inl tt)
| RmNo : forall err, results_match None (inr err).

Lemma results_match_chain : forall A B x y
    (f : option A -> option B)
    (g : unit + type_error -> unit + type_error),
    (forall x, exists x', f (Some x) = Some x') ->
    (f None = None) ->
    (g (inl tt) = inl tt) ->
    (forall y, exists y', g (inr y) = inr y') ->
    results_match x y ->
    results_match (f x) (g y).
intros0 Hf Hf' Hg Hg' Hrm.

invc Hrm.
- destruct (Hf x0) as [? Hf_x]. rewrite Hf_x, Hg. constructor.
- destruct (Hg' err) as [? Hg'_y]. rewrite Hf', Hg'_y. constructor.
Qed.

Lemma results_match_chain' : forall A B
        (x1 : option A) (x2 : option B)
        (y1 y2 : unit + type_error),
    (forall x, x1 = Some x -> exists x', x2 = Some x') ->
    (x1 = None -> x2 = None) ->
    (y1 = inl tt -> y2 = inl tt) ->
    (forall y, y1 = inr y -> exists y', y2 = inr y') ->
    results_match x1 y1 ->
    results_match x2 y2.
intros0 Hx Hx' Hy Hy' Hrm.

invc Hrm.
- destruct (Hx x) as [? Hx_x]; auto. rewrite Hx_x, Hy; auto. constructor.
- destruct (Hy' err) as [? Hy'_y]; auto. rewrite Hx', Hy'_y; auto. constructor.
Qed.

Lemma results_match_chain_l : forall A B x y
    (f : option A -> option B),
    (forall x, exists x', f (Some x) = Some x') ->
    (f None = None) ->
    results_match x y ->
    results_match (f x) y.
intros. change y with (id y). eapply results_match_chain; eauto.
unfold id. eauto.
Qed.

Lemma results_match_chain_r : forall A (x : option A) y
    (g : unit + type_error -> unit + type_error),
    (g (inl tt) = inl tt) ->
    (forall y, exists y', g (inr y) = inr y') ->
    results_match x y ->
    results_match x (g y).
intros. change x with (id x). eapply results_match_chain; eauto.
unfold id. eauto.
Qed.

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


Ltac lift xx :=
    let T := type of xx in
    let switch old new_f :=
        let new_f' := eval cbv beta in new_f in
        (change old with (new_f' xx)) in

    match goal with
    | [ |- context [?f (?fx xx) ?b ?c ?d ?e] ] =>
            switch (f (fx xx) b c d e) (fun x : T => f (fx x) b c d e)
    | [ |- context [?f ?a (?fx xx) ?c ?d ?e] ] =>
            switch (f a (fx xx) c d e) (fun x : T => f a (fx x) c d e)
    | [ |- context [?f ?a ?b (?fx xx) ?d ?e] ] =>
            switch (f a b (fx xx) d e) (fun x : T => f a b (fx x) d e)
    | [ |- context [?f ?a ?b ?c (?fx xx) ?e] ] =>
            switch (f a b c (fx xx) e) (fun x : T => f a b c (fx x) e)
    | [ |- context [?f ?a ?b ?c ?d (?fx xx)] ] =>
            switch (f a b c d (fx xx)) (fun x : T => f a b c d (fx x))

    | [ |- context [?f (?fx xx) ?b ?c ?d] ] =>
            switch (f (fx xx) b c d) (fun x : T => f (fx x) b c d)
    | [ |- context [?f ?a (?fx xx) ?c ?d] ] =>
            switch (f a (fx xx) c d) (fun x : T => f a (fx x) c d)
    | [ |- context [?f ?a ?b (?fx xx) ?d] ] =>
            switch (f a b (fx xx) d) (fun x : T => f a b (fx x) d)
    | [ |- context [?f ?a ?b ?c (?fx xx)] ] =>
            switch (f a b c (fx xx)) (fun x : T => f a b c (fx x))

    | [ |- context [?f (?fx xx) ?b ?c] ] =>
            switch (f (fx xx) b c) (fun x : T => f (fx x) b c)
    | [ |- context [?f ?a (?fx xx) ?c] ] =>
            switch (f a (fx xx) c) (fun x : T => f a (fx x) c)
    | [ |- context [?f ?a ?b (?fx xx)] ] =>
            switch (f a b (fx xx)) (fun x : T => f a b (fx x))

    | [ |- context [?f (?fx xx) ?b] ] =>
            switch (f (fx xx) b) (fun x : T => f (fx x) b)
    | [ |- context [?f ?a (?fx xx)] ] =>
            switch (f a (fx xx)) (fun x : T => f a (fx x))

    | [ |- context [?f (?fx xx)] ] =>
            switch (f (fx xx)) (fun x : T => f (fx x))

    | [ |- context [xx] ] =>
            switch (xx) (fun x : T => x)
    end.



Lemma type_umicro_checked_correct : forall dbt rt uop,
    results_match (type_umicro dbt rt uop) (type_umicro_checked dbt rt uop).
intros dbt rt.
induction uop using umicro_rec' with
    (Pl := fun uops =>
        results_match
            (type_umicro_list dbt rt uops)
            (map_checked (type_umicro_checked dbt rt) uops));
simpl;
fold (type_umicro_list dbt rt);
fold (map_checked (type_umicro_checked dbt rt));
try solve [constructor; discriminate 1 || eauto].

- destruct (lookup_type _ _); simpl;
  constructor; discriminate 1 || eauto.

- destruct (lookup_type _ _); simpl;
  constructor; discriminate 1 || eauto.

- destruct (lookup_type _ _); simpl;
  [ destruct (find_match_for_type _ _); simpl | ];
  constructor; discriminate 1 || eauto.

- do 2 lift (type_umicro_list dbt rt body).
  eapply results_match_chain_l with (3 := IHuop); simpl; eauto.

- do 2 lift (type_umicro_list dbt rt code).
  eapply results_match_chain_l with (3 := IHuop); simpl; eauto.

- destruct (lookup_type _ _); simpl;
  constructor; discriminate 1 || eauto.

- unfold bind_option.
  invc IHuop; invc IHuop0; simpl; constructor.

Qed.

Lemma map_checked_correct : forall A B (f : A -> option B) f' xs,
    (forall x, results_match (f x) (f' x)) ->
    results_match (map_opt f xs) (map_checked f' xs).
induction xs; intros0 Hrm.
- constructor; simpl; intros; discriminate || eauto.
- specialize (IHxs Hrm). rename a into x. specialize (Hrm x).
  simpl. unfold bind_option.
  invc Hrm; invc IHxs; simpl; constructor.
Qed.

Lemma type_record_uprogram_checked_correct : forall dbt urp,
    results_match (type_record_uprogram dbt urp)
                  (type_record_uprogram_checked dbt urp).
intros. unfold type_record_uprogram, type_record_uprogram_checked.
do 2 lift (map_opt (type_umicro dbt (ru_type urp)) (ru_code urp)).
eapply results_match_chain_l; simpl; eauto.
eapply map_checked_correct. eapply type_umicro_checked_correct.
Qed.

(*
Lemma chain_map_checked_numbered' : forall A B (f : A -> option B) f' xs n,
    results_match (map_opt f xs) (map_checked f' xs) ->
    results_match (map_opt f xs) (map_checked (check_numbered_record f') (numbered' n xs)).
induction xs; intros0 Hrm.
- constructor; simpl; intros; discriminate || eauto.
- simpl in *; unfold bind_option in *.
  destruct (f a), (map_opt f xs),
    (f' a), (map_checked f' xs) eqn:?, (map_checked _ (numbered' _ xs)) eqn:?;
    (repeat on unit, fun H => destruct H); try econstructor; invc Hrm.
  + specialize (IHxs (S n) ltac:(constructor)). rewrite Heqs0 in IHxs. invc IHxs.
  + specialize (IHxs (S n) ltac:(constructor)). rewrite Heqs0 in IHxs. invc IHxs.
  + specialize (IHxs (S n) ltac:(constructor)). rewrite Heqs0 in IHxs. invc IHxs.
  + 
    try destruct u; try destruct u0; try try discriminate.
  destruct (f a), (f' a); try destruct u.
  Focus 2.
  eapply 

  + destruct (f a), (map_opt f xs), (f' a), (map_checked f' xs);
      try destruct u; try destruct u0; try discriminate.
    specialize (IHxs (S n) ltac:(constructor)). invc IHxs.
    econstructor.

  + destruct (f a), (map_opt f xs), (f' a), (map_checked f' xs);
      try destruct u; try destruct u0; try discriminate.
    all: try (specialize (IHxs (S n) ltac:(constructor)); invc IHxs; constructor).
    econstructor.

simpl in *. unfold bind_option in *.
destruct (f a) eqn:?, (f' a) eqn:?; try destruct u.
destruct (map_opt f xs), (map_checked _ _); try destruct u.
  *)

Lemma map_checked_numbered'_inl : forall A (f : A -> _) xs n,
    map_checked f xs = inl tt ->
    map_checked (check_numbered_record f) (numbered' n xs) = inl tt.
induction xs; intros0 Hmap; simpl in *.  { auto. }
destruct (f a), (map_checked f xs) eqn:?;
(repeat on unit, fun H => destruct H); try discriminate.
rewrite IHxs; eauto.
Qed.

Lemma map_checked_numbered_inl : forall A (f : A -> _) xs,
    map_checked f xs = inl tt ->
    map_checked (check_numbered_record f) (numbered xs) = inl tt.
unfold numbered. intros. eapply map_checked_numbered'_inl; eauto.
Qed.

Lemma map_checked_numbered'_inr : forall A (f : A -> _) xs n err,
    map_checked f xs = inr err ->
    exists err',
        map_checked (check_numbered_record f) (numbered' n xs) = inr err'.
induction xs; intros0 Hmap; simpl in *.  { discriminate. }
destruct (f a), (map_checked f xs) eqn:?;
(repeat on unit, fun H => destruct H); try discriminate.
- destruct (IHxs (S n) ?? ***) as (? & Heq). rewrite Heq. eauto.
- break_match; try destruct u; eauto.
- break_match; try destruct u; eauto.
Qed.

Lemma map_checked_numbered_inr : forall A (f : A -> _) xs err,
    map_checked f xs = inr err ->
    exists err',
        map_checked (check_numbered_record f) (numbered xs) = inr err'.
unfold numbered. intros. eapply map_checked_numbered'_inr; eauto.
Qed.

Lemma type_database_program'_checked_correct : forall dbt udp,
    results_match (type_database_program' dbt udp)
                  (type_database_program'_checked dbt udp).
intros. unfold type_database_program', type_database_program'_checked.
assert (HH : results_match
        (map_opt (type_record_uprogram dbt) udp)
        (map_checked (type_record_uprogram_checked dbt) udp)).
  { eapply map_checked_correct. eapply type_record_uprogram_checked_correct. }

eapply results_match_chain' with (5 := HH); eauto.
- eapply map_checked_numbered_inl.
- eapply map_checked_numbered_inr.
Qed.

Lemma type_database_program_checked_correct : forall udp,
    results_match (type_database_program udp)
                  (type_database_program_checked udp).
intros. unfold type_database_program, type_database_program_checked.
eapply type_database_program'_checked_correct.
Qed.


Definition unwrap_matched_results {A} x y :
    @results_match A x y ->
    A + type_error.
intro Hrm.
refine (
    match x as x_, y as y_ return x = x_ -> y = y_ -> _ with
    | Some val, inl tt => fun _ _ => inl val
    | None, inr err => fun _ _ => inr err
    | _, _ => fun Heq1 Heq2 => _
    end eq_refl eq_refl
); hide; exfalso; subst; invc Hrm.
Defined.
Implicit Arguments unwrap_matched_results [A].

Lemma unwrap_matched_results_inl : forall A x y pf val,
    @unwrap_matched_results A x y pf = inl val ->
    x = Some val.
intros0 Hunwrap.
unfold unwrap_matched_results in Hunwrap.
destruct x, y; (repeat on unit, fun u => destruct u); try solve [discriminate | invc pf].
congruence.
Qed.


Definition type_database_program_with_check udp :=
    unwrap_matched_results
        (type_database_program udp)
        (type_database_program_checked udp)
        ltac:(eauto using type_database_program_checked_correct).

Lemma type_database_program_with_check_inl_eq udp dbp :
    type_database_program_with_check udp = inl dbp ->
    type_database_program udp = Some dbp.
unfold type_database_program_with_check. eapply unwrap_matched_results_inl.
Qed.

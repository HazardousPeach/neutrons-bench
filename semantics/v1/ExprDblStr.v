Require Import List.
Import ListNotations.
Require Import String.
Require Import Flocq.Appli.Fappli_IEEE_bits.
Require Import Flocq.Appli.Fappli_IEEE.
Require Import ZArith.

Require Import v1.EpicsTypes.
Require Import v1.Multi.
Require Import v1.NeutronTactics.
Require Import v1.FloatAux.
Require Import v1.Util.

Require Import v1.Expr.
Require v1.ExprDbl.  (* reuse some of the double arithmetic functions *)


Inductive ty := Nil | Dbl | Str.
Scheme Equality for ty.

Definition require_not_nil x :=
    match x with
    | Nil => None
    | _ => Some x
    end.

Definition require_dbl x :=
    match x with
    | Dbl => Some Dbl
    | _ => None
    end.

Definition require_match y x :=
    if ty_eq_dec x y then Some x else None.

Definition always (x : ty) := fun (_ : ty) => Some x.

Definition unary_op_type (op : unary_op) (arg : ty) : option ty :=
    match op with
    | NotAlg => require_dbl arg
    | NotLog => require_dbl arg
    end.

Definition binary_op_type (op : binary_op) arg1 arg2 :=
    match op with
    | Add => require_not_nil arg1 >>= require_match arg2
    | Sub => require_dbl arg1 >>= require_match arg2
    | Mul => require_dbl arg1 >>= require_match arg2
    | Div => require_dbl arg1 >>= require_match arg2
    | Ge => require_dbl arg1 >>= require_match arg2
    | Gt => require_dbl arg1 >>= require_match arg2
    | Le => require_dbl arg1 >>= require_match arg2
    | Lt => require_dbl arg1 >>= require_match arg2
    | Ne => require_not_nil arg1 >>= require_match arg2 >>= always Dbl
    | Eq => require_not_nil arg1 >>= require_match arg2 >>= always Dbl
    | AndLog => require_dbl arg1 >>= require_match arg2
    | OrLog => require_dbl arg1 >>= require_match arg2
    end.

Definition varary_op_type (op : varary_op) (args : list ty) :=
    match op return option ty with
    | Min => None (* TODO *)
    | Max => None (* TODO *)
    end.

Definition seq_result_type t1 t2 :=
    match t1, t2 with
    | Nil, x => Some x
    | x, Nil => Some x
    | _, _ => None      (* Error to have two subexpressions that both produce results *)
    end.

Inductive well_typed {n : nat} : ty -> expr (e_double + e_string) n -> Prop :=
| WtVar : forall i, well_typed Dbl (EVar i)
| WtEVar : forall i, well_typed Str (EXVar i)
| WtLitDbl : forall x, well_typed Dbl (ELit (inl x))
| WtLitStr : forall x, well_typed Str (ELit (inr x))
| WtUnary : forall op t x t',
        unary_op_type op t = Some t' ->
        well_typed t x -> 
        well_typed t' (EUnary op x)
| WtBinary : forall op t1 x1 t2 x2 t',
        binary_op_type op t1 t2 = Some t' ->
        well_typed t1 x1 -> 
        well_typed t2 x2 -> 
        well_typed t' (EBinary op x1 x2)
| WtVarary : forall op ts xs t',
        varary_op_type op ts = Some t' ->
        Forall2 well_typed ts xs ->
        well_typed t' (EVarary op xs)
| WtAssign : forall i x,
        well_typed Dbl x ->
        well_typed Nil (EAssign i x)
| WtXAssign : forall i x,
        well_typed Str x ->
        well_typed Nil (EXAssign i x)
| WtCond : forall t cond body1 body2,
        well_typed Dbl cond ->
        well_typed t body1 ->
        well_typed t body2 ->
        well_typed t (ECond cond body1 body2)
| WtSeq : forall t1 e1 t2 e2 t,
        well_typed t1 e1 ->
        well_typed t2 e2 ->
        seq_result_type t1 t2 = Some t ->
        well_typed t (ESeq e1 e2)
.

Fixpoint count_results {n} (e : expr e_double n) :=
    match e with
    | EAssign _ _ => 0
    | EXAssign _ _ => 0
    | ESeq e1 e2 => count_results e1 + count_results e2
    | _ => 1
    end.






Notation b64_eq := (ExprDbl.b64_eq) (only parsing).
Notation b64_ne := (ExprDbl.b64_eq) (only parsing).
Notation b64_lt := (ExprDbl.b64_eq) (only parsing).
Notation b64_le := (ExprDbl.b64_eq) (only parsing).
Notation b64_gt := (ExprDbl.b64_eq) (only parsing).
Notation b64_ge := (ExprDbl.b64_eq) (only parsing).

Notation b64_and := (ExprDbl.b64_and) (only parsing).
Notation b64_or := (ExprDbl.b64_or) (only parsing).


Definition denote_ty t :=
    match t with
    | Nil => unit
    | Dbl => e_double
    | Str => e_string
    end.


Inductive unary_denotation : ty -> Set :=
| UnaryD (t t' : ty) (f : denote_ty t -> denote_ty t') :
        unary_denotation t
.

Definition double_unary t t' (f : e_double -> denote_ty t') :
        option (unary_denotation t) :=
    match t with
    | Dbl => Some (UnaryD Dbl t' f)
    | _ => None
    end.

Definition denote_unary_op op t : option (unary_denotation t) :=
    match op with
    | NotAlg => double_unary t Dbl (fun x => b64_opp x)
    | NotLog => double_unary t Dbl (fun x => if is_zero x then one else zero)
    end.


Inductive binary_denotation : ty -> ty -> Set :=
| BinaryD (t1 t2 t' : ty) (f : denote_ty t1 -> denote_ty t2 -> denote_ty t') :
        binary_denotation t1 t2
.

Definition double_binary t1 t2 t' (f : e_double -> e_double -> denote_ty t') :
        option (binary_denotation t1 t2) :=
    match t1, t2 with
    | Dbl, Dbl => Some (BinaryD Dbl Dbl t' f)
    | _, _ => None
    end.

Definition denote_binary_op op t1 t2 : option (binary_denotation t1 t2) :=
    match op with
    | Add => match t1, t2 with
        | Dbl, Dbl => Some (BinaryD Dbl Dbl Dbl (b64_plus mode_NE))
        | Str, Str => Some (BinaryD Str Str Str append)
        | _, _ => None
        end
    | Sub => double_binary t1 t2 Dbl (b64_minus mode_NE)
    | Mul => double_binary t1 t2 Dbl (b64_mult mode_NE)
    | Div => double_binary t1 t2 Dbl (b64_div mode_NE)
    | Ge => double_binary t1 t2 Dbl b64_ge
    | Gt => double_binary t1 t2 Dbl b64_gt
    | Le => double_binary t1 t2 Dbl b64_le
    | Lt => double_binary t1 t2 Dbl b64_lt
    | Ne => match t1, t2 with
        | Dbl, Dbl => Some (BinaryD Dbl Dbl Dbl b64_ne)
        | Str, Str => Some (BinaryD Str Str Dbl
                (fun a b => if string_dec a b then zero else one))
        | _, _ => None
        end
    | Eq => match t1, t2 with
        | Dbl, Dbl => Some (BinaryD Dbl Dbl Dbl b64_eq)
        | Str, Str => Some (BinaryD Str Str Dbl
                (fun a b => if string_dec a b then one else zero))
        | _, _ => None
        end
    | AndLog => double_binary t1 t2 Dbl b64_and
    | OrLog => double_binary t1 t2 Dbl b64_or
    end.



Definition state_fn n A :=
    (multi n e_double -> multi n e_string ->
     multi n e_double * multi n e_string * A)%type.

Inductive denotation n :=
| Denot (t : ty) (f : state_fn n (denote_ty t))
.
Implicit Arguments Denot [n].

Definition double_f {n} (x : option (denotation n))  :=
    match x with
    | Some (Denot t f) =>
            match t as t_ return state_fn n (denote_ty t_) -> _ with
            | Dbl => fun f => Some f
            | _ => fun _ => None
            end f
    | None => None
    end.

Definition string_f {n} (x : option (denotation n))  :=
    match x with
    | Some (Denot t f) =>
            match t as t_ return state_fn n (denote_ty t_) -> _ with
            | Str => fun f => Some f
            | _ => fun _ => None
            end f
    | None => None
    end.

Definition unpack_denot {n} (d : option (denotation n))
        (f : forall (t : ty), state_fn n (denote_ty t) -> option (denotation n)) :
        option (denotation n) :=
    match d with
    | Some (Denot t f') => f t f'
    | None => None
    end.

Definition pack_denot {n} t (f : state_fn n (denote_ty t)) := Some (@Denot n t f).

Definition unpack_unary {n} {t} (d : option (unary_denotation t))
        (f : forall (t' : ty), (denote_ty t -> denote_ty t') -> option (denotation n)) :
        option (denotation n).
destruct d as [ d | ]; [ | exact None ].
destruct d. destruct t'; eapply f; eassumption.
Defined.

Definition unpack_binary {n} {t1 t2} (d : option (binary_denotation t1 t2))
        (f : forall (t' : ty), (denote_ty t1 -> denote_ty t2 -> denote_ty t') ->
            option (denotation n)) :
        option (denotation n).
destruct d as [ d | ]; [ | exact None ].
destruct d. destruct t'; eapply f; eassumption.
Defined.

Fixpoint denote' {n} (e : expr (e_double + e_string) n) : option (denotation n) :=
    match e with
    | EVar i => pack_denot Dbl (fun sd ss => (sd, ss, sd !! i))
    | EXVar i => pack_denot Str (fun sd ss => (sd, ss, ss !! i))
    | ELit (inl d) => pack_denot Dbl (fun sd ss => (sd, ss, d))
    | ELit (inr s) => pack_denot Str (fun sd ss => (sd, ss, s))
    | EUnary op xe =>
            unpack_denot (denote' xe) (fun xt xf =>
            unpack_unary (denote_unary_op op xt) (fun t' opf =>
            pack_denot t'
                (fun sd ss =>
                    let '(sd', ss', x) := xf sd ss in
                    (sd', ss', opf x))))
    | EBinary op xe ye =>
            unpack_denot (denote' xe) (fun xt xf =>
            unpack_denot (denote' ye) (fun yt yf =>
            unpack_binary (denote_binary_op op xt yt) (fun t' opf =>
            pack_denot t'
                (fun sd ss =>
                    let '(sd', ss', x) := xf sd ss in
                    let '(sd'', ss'', y) := yf sd' ss' in
                    (sd'', ss'', opf x y)))))
    | EVarary _ _ => None (* unsupported *)
    | EAssign i xe =>
            double_f (denote' xe) >>= fun xf =>
            pack_denot Nil (fun sd ss =>
                let '(sd', ss', x) := xf sd ss in
                (multi_set sd' i x, ss', tt))
    | EXAssign i xe =>
            string_f (denote' xe) >>= fun xf =>
            pack_denot Nil (fun sd ss =>
                let '(sd', ss', x) := xf sd ss in
                (sd', multi_set ss' i x, tt))
    | ECond ce xe ye =>
            double_f (denote' ce) >>= fun cf =>
            unpack_denot (denote' xe) (fun xt xf =>
            unpack_denot (denote' ye) (fun yt yf =>
            if ty_eq_dec xt yt then
                pack_denot xt
                    ltac:(subst; refine (fun sd ss =>
                        let '(sd', ss', c) := cf sd ss in
                        if negb (is_zero c) then xf sd' ss' else yf sd' ss'))
            else
                None))
    | ESeq xe ye =>
            unpack_denot (denote' xe) (fun xt xf =>
            unpack_denot (denote' ye) (fun yt yf =>
            match xt, yt with
            | Nil, _ =>
                    pack_denot yt
                        (fun sd ss =>
                            let '(sd', ss', _) := xf sd ss in
                            let '(sd'', ss'', y) := yf sd' ss' in
                            (sd'', ss'', y))
            | _, Nil =>
                    pack_denot xt
                        (fun sd ss =>
                            let '(sd', ss', x) := xf sd ss in
                            let '(sd'', ss'', _) := yf sd' ss' in
                            (sd'', ss'', x))
            | _, _ => None (* both sides evaluate to results *)
            end))
    end.

Definition denote {n} (e : expr (e_double + e_string) n) :
    option (state_fn n (e_double + e_string)) :=
    match denote' e with
    | Some (Denot Dbl f) => Some (fun sd ss =>
            let '(sd', ss', x) := f sd ss in
            (sd', ss', inl x))
    | Some (Denot Str f) => Some (fun sd ss =>
            let '(sd', ss', x) := f sd ss in
            (sd', ss', inr x))
    | _ => None
    end.


Lemma denote_unary_op_ok : forall op t t',
    unary_op_type op t = Some t' ->
    exists f, denote_unary_op op t = Some (UnaryD t t' f).
destruct op; simpl in *; try discriminate;
destruct t; simpl in *; try discriminate;
intros0 Hty; fancy_injr <- Hty; eauto.
Qed.

Lemma denote_binary_op_ok : forall op t1 t2 t',
    binary_op_type op t1 t2 = Some t' ->
    exists f, denote_binary_op op t1 t2 = Some (BinaryD t1 t2 t' f).
destruct op; simpl in *; try discriminate;
destruct t1; simpl in *; try discriminate;
destruct t2; simpl in *; try discriminate;
intros0 Hty; compute in Hty; fancy_injr <- Hty; eauto.
Qed.

Lemma denote_valid_unary_op_rev : forall op t t' f,
    denote_unary_op op t = Some (UnaryD t t' f) ->
    unary_op_type op t = Some t'.
destruct op; simpl in *; try discriminate;
destruct t; simpl in *; try discriminate;
intros0 Hd; inversion Hd; eauto.
Qed.

Lemma denote_valid_binary_op_rev : forall op t1 t2 t' f,
    denote_binary_op op t1 t2 = Some (BinaryD t1 t2 t' f) ->
    binary_op_type op t1 t2 = Some t'.
destruct op; simpl in *; try discriminate;
destruct t1; simpl in *; try discriminate;
destruct t2; simpl in *; try discriminate;
intros0 Hd; inversion Hd; eauto.
Qed.

Theorem well_typed_denote' : forall n (e : expr (e_double + e_string) n) t,
    well_typed t e ->
    exists f, denote' e = Some (Denot t f).
intro n.
induction e; intros0 Hwt; try invc Hwt.

- compute [denote denote' pack_denot]. eauto.
- compute [denote denote' pack_denot]. eauto.
- compute [denote denote' pack_denot]. eauto.
- compute [denote denote' pack_denot]. eauto.

- (* EUnary *) simpl.
  forward eapply IHe as [ef Hef]; eauto. rewrite Hef. simpl.
  forward eapply denote_unary_op_ok as [opf Hopf]; eauto. rewrite Hopf. simpl.
  destruct t; unfold pack_denot; eauto.

- (* EBinary *) simpl.
  forward eapply IHe1 as [e1f He1f]; eauto. rewrite He1f. simpl.
  forward eapply IHe2 as [e2f He2f]; eauto. rewrite He2f. simpl.
  forward eapply denote_binary_op_ok as [opf Hopf]; eauto. rewrite Hopf. simpl.
  destruct t; unfold pack_denot; eauto.

- (* EVarary *) simpl. destruct v; try discriminate.

- (* EAssign *) simpl.
  forward eapply IHe as [ef Hef]; eauto. rewrite Hef. simpl.
  unfold pack_denot; eauto.

- (* EXAssign *) simpl.
  forward eapply IHe as [ef Hef]; eauto. rewrite Hef. simpl.
  unfold pack_denot; eauto.

- (* ECond *) simpl.
  forward eapply IHe1 as [e1f He1f]; eauto. rewrite He1f. simpl.
  forward eapply IHe2 as [e2f He2f]; eauto. rewrite He2f. simpl.
  forward eapply IHe3 as [e3f He3f]; eauto. rewrite He3f. simpl.
  break_match; try congruence.
  unfold pack_denot; eauto.

- (* ESeq *) simpl.
  forward eapply IHe1 as [e1f He1f]; eauto. rewrite He1f. simpl.
  forward eapply IHe2 as [e2f He2f]; eauto. rewrite He2f. simpl.
  destruct t1, t2; (on (seq_result_type _ _ = _), fun H =>
        try discriminate H; simpl in H; fancy_injr <- H);
  unfold pack_denot; eauto.

Qed.

Theorem well_typed_denote : forall n (e : expr (e_double + e_string) n),
    (well_typed Dbl e \/ well_typed Str e) -> exists f, denote e = Some f.
intros0 Hwt. destruct Hwt;
forward eapply well_typed_denote' as [f Hf]; eauto;
    unfold denote; rewrite Hf; eauto.
Qed.

Definition denote_total n (e : expr (e_double + e_string) n) :
    (well_typed Dbl e \/ well_typed Str e) ->
    { f | denote e = Some f }.
intros0 Hwt.
forward eapply well_typed_denote; eauto.
destruct (denote _) eqn:?.
- eauto.
- exfalso. break_exists. discriminate.
Defined.


Section typecheck.
Open Scope string.

Definition ty_name t :=
    match t with
    | Nil => "Nil"
    | Dbl => "Dbl"
    | Str => "Str"
    end.

Local Definition concat xs := fold_left append xs "".

Local Ltac require_type t t' loc :=
    destruct t eqn:?;
    match goal with
    | [ H : t = t' |- _ ] => clear H
    | [ |- _ ] =>
            (* We're in the case where `t` is something other than `t'` *)
            right; exact (concat ["bad type in "; loc; ": got "; ty_name t;
                " but expected "; ty_name t' ])
    end.

Definition typecheck_expr' n (e : expr (e_double + e_string) n) :
    { t | well_typed t e } + string.
induction e using expr_rect_mut with (Pl := fun _ => unit).

- left. eexists. constructor.
- left. eexists. constructor.
- destruct x.
  + left. eexists. constructor.
  + left. eexists. constructor.

- destruct IHe as [[t ?]| ? ]; [ | right; assumption ].
  destruct (unary_op_type op t) as [ t' | ] eqn:?;
      [ | right; exact (concat ["unary op "; unary_op_name op;
              " can't apply to ("; ty_name t; ")"]) ].
  left. exists t'. econstructor; eassumption.

- destruct IHe1 as [[t1 ?]| ? ]; [ | right; assumption ].
  destruct IHe2 as [[t2 ?]| ? ]; [ | right; assumption ].
  destruct (binary_op_type op t1 t2) as [ t' | ] eqn:?;
      [ | right; exact (concat ["unary op "; binary_op_name op;
              " can't apply to ("; ty_name t1; ", "; ty_name t2; ")"]) ].
  left. exists t'. econstructor; eassumption.

- right; exact "varary ops are not yet supported".

- destruct IHe as [[t ?] | ?]; [ require_type t Dbl "rhs of assign" | right; assumption ].
  left. eexists. constructor. assumption.

- destruct IHe as [[t ?] | ?]; [ require_type t Str "rhs of xassign" | right; assumption ].
  left. eexists. constructor. assumption.

- destruct IHe1 as [[t1 ?] | ?]; [ require_type t1 Dbl "condition of cond" | right; assumption ].
  destruct IHe2 as [[t2 ?] | ?]; [ | right; assumption ].
  destruct IHe3 as [[t3 ?] | ?]; [ | right; assumption ].
  destruct (ty_eq_dec t2 t3).
  + left. eexists. constructor; eauto. congruence.
  + right. exact (concat ["conditional branches have mismatched types: ";
              ty_name t1; " <> "; ty_name t2]).

- destruct IHe1 as [[t1 ?] | ?]; [ | right; assumption ].
  destruct IHe2 as [[t2 ?] | ?]; [ | right; assumption ].
  destruct (seq_result_type t1 t2) as [ t' | ] eqn:?;
          [ | right; exact "multiple result values in seq" ].
  left. eexists. econstructor; eauto.

- exact tt.
- exact tt.

Qed.

Definition typecheck_expr n (e : expr (e_double + e_string) n) :
    (well_typed Dbl e \/ well_typed Str e) + string.
destruct (typecheck_expr' n e) as [[t ?] | ?].
- destruct t.
  + right. exact "no subexpression produced a value".
  + left. left. assumption.
  + left. right. assumption.
- right. assumption.
Qed.

End typecheck.

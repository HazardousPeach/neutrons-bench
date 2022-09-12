Require Import List.
Import ListNotations.
Require Import v1.Multi.

Set Implicit Arguments.

Inductive unary_op :=
(* | Abs | Sqr | Ceil | Floor *)
(* | Log | Ln | Exp *)
| NotAlg
(* | Sin | SinH | ASin *)
(* | Cos | CosH | ACos *)
(* | Tan | TanH | ATan *)
| NotLog
(* | NotBit *)
.

Inductive binary_op :=
(* | Pow *)
| Add | Sub | Mul | Div (* | Mod *)
| Ge | Gt | Le | Lt | Ne | Eq
| AndLog | OrLog
(* | OrBit | AndBit | XorBit *)
(* | ShiftL | ShiftR *)
(* | Printf *)
.

Inductive ternary_op :=
| Cond
(* TODO *)
.

Inductive varary_op :=
| Min | Max
(* | Finite | IsNan *)
.

Inductive expr {A : Type} {n : nat} : Type :=
| EVar : index n -> expr
| EXVar : index n -> expr
| ELit : A -> expr
| EUnary : unary_op -> expr -> expr
| EBinary : binary_op -> expr -> expr -> expr
| EVarary : varary_op -> list expr -> expr
| EAssign : index n -> expr -> expr
| EXAssign : index n -> expr -> expr
| ECond : expr -> expr -> expr -> expr
| ESeq : expr -> expr -> expr
.
Implicit Arguments expr.

Definition expr_rect_mut A n (P : expr A n -> Type) (Pl : list (expr A n) -> Type)
    (HVar :     forall i, P (EVar i))
    (HXVar :    forall i, P (EXVar i))
    (HLit :     forall x, P (ELit x))
    (HUnary :   forall op x, P x -> P (EUnary op x))
    (HBinary :  forall op x y, P x -> P y -> P (EBinary op x y))
    (HVarary :  forall op xs, Pl xs -> P (EVarary op xs))
    (HAssign :  forall i x, P x -> P (EAssign i x))
    (HXAssign : forall i x, P x -> P (EXAssign i x))
    (HCond :    forall c t f, P c -> P t -> P f -> P (ECond c t f))
    (HSeq :     forall e1 e2, P e1 -> P e2 -> P (ESeq e1 e2))
    (Hnil :     Pl [])
    (Hcons :    forall e es, P e -> Pl es -> Pl (e :: es))
    e : P e :=
    let fix go e :=
        let fix go_list es :=
            match es as es_ return Pl es_ with
            | [] => Hnil
            | e :: es => Hcons e es (go e) (go_list es)
            end in
        match e as e_ return P e_ with
        | EVar i => HVar i
        | EXVar i => HXVar i
        | ELit x => HLit x
        | EUnary op x => HUnary op x (go x)
        | EBinary op x y => HBinary op x y (go x) (go y)
        | EVarary op xs => HVarary op xs (go_list xs)
        | EAssign i x => HAssign i x (go x)
        | EXAssign i x => HXAssign i x (go x)
        | ECond c t f => HCond c t f (go c) (go t) (go f)
        | ESeq e1 e2 => HSeq e1 e2 (go e1) (go e2)
        end in go e.

Section names.
Require Import String.
Open Scope string.

Definition unary_op_name op :=
    match op with
    | NotAlg => "NotAlg"
    | NotLog => "NotLog"
    end.

Definition binary_op_name op :=
    match op with
    | Add => "Add"
    | Sub => "Sub"
    | Mul => "Mul"
    | Div => "Div"
    | Ge => "Ge"
    | Gt => "Gt"
    | Le => "Le"
    | Lt => "Lt"
    | Ne => "Ne"
    | Eq => "Eq"
    | AndLog => "AndLog"
    | OrLog => "OrLog"
    end.

Definition varary_op_name (op : varary_op) : string :=
    match op with
    | Min => "Min"
    | Max => "Max"
    end.

End names.



Definition unop_impl {A} (denote : A -> Set) (ty1 tyR : A) :=
    denote ty1 -> denote tyR.
Definition unop_denotation {A} (denote : A -> Set) (ty1 : A) :=
    { tyR : A & unop_impl denote ty1 tyR }.

Definition binop_impl {A} (denote : A -> Set) (ty1 ty2 tyR : A) :=
    denote ty1 -> denote ty2 -> denote tyR.
Definition binop_denotation {A} (denote : A -> Set) (ty1 ty2 : A) :=
    { tyR : A & binop_impl denote ty1 ty2 tyR }.

Definition ternop_impl {A} (denote : A -> Set) (ty1 ty2 ty3 tyR : A) :=
    denote ty1 -> denote ty2 -> denote ty3 -> denote tyR.
Definition ternop_denotation {A} (denote : A -> Set) (ty1 ty2 ty3 : A) :=
    { tyR : A & ternop_impl denote ty1 ty2 ty3 tyR }.

Definition varop_impl {A} (denote : A -> Set) (ty1 tyR : A) :=
    list (denote ty1) -> denote tyR.
Definition varop_denotation {A} (denote : A -> Set) (ty1 : A) :=
    { tyR : A & varop_impl denote ty1 tyR }.

Record eval_bits {A : Type} := EvalBits
    { tydesc : Set
    ; tydesc_eq_dec : forall (x y : tydesc), { x = y } + { x <> y }
    ; ty_denote : tydesc -> Set

    ; var_ty : tydesc
    ; xvar_ty : tydesc
    ; convert_lit : A -> { ty : tydesc & ty_denote ty }

    ; nil_ty : tydesc
    ; nil_value : ty_denote nil_ty

    ; unop_denote : unary_op -> forall (ty1 : tydesc),
        option (unop_denotation ty_denote ty1)
    ; binop_denote : binary_op -> forall (ty1 ty2 : tydesc),
        option (binop_denotation ty_denote ty1 ty2)
    ; ternop_denote : ternary_op -> forall (ty1 ty2 ty3 : tydesc),
        option (ternop_denotation ty_denote ty1 ty2 ty3)
    ; varop_denote : varary_op -> forall (ty1 : tydesc),
        option (varop_denotation ty_denote ty1)
    }.
Implicit Arguments eval_bits.


Section denote.
Variable A : Set.
Variable D : eval_bits A.
Variable n : nat.

Let tydesc := tydesc D.
Let tydesc_eq_dec := tydesc_eq_dec D.
Let ty_denote := ty_denote D.
Let var_ty := var_ty D.
Let xvar_ty := xvar_ty D.
Let var_ty' := ty_denote var_ty.
Let xvar_ty' := ty_denote xvar_ty.
Let convert_lit := convert_lit D.

Let nil_ty := nil_ty D.
Let nil_ty' := ty_denote nil_ty.
Let nil := nil_value D.

Let unop_denote := unop_denote D.
Let binop_denote := binop_denote D.
Let ternop_denote := ternop_denote D.
Let varop_denote := varop_denote D.

Definition state_fn A :=
    (multi n var_ty' -> multi n xvar_ty' ->
     multi n var_ty' * multi n xvar_ty' * A)%type.

Definition state_fn_noxvar A :=
    (multi n var_ty' ->
     multi n var_ty' * A)%type.

Definition denotation := { ty : tydesc & state_fn (ty_denote ty) }.

Definition denotation_list := { ty : tydesc & state_fn (list (ty_denote ty)) }.

Definition unpack {B P R} (s : { x : B & P x })
        (f : forall (x : B), P x -> R) : R :=
    match s with
    | existT _ x y => f x y
    end.

Definition unpack_opt {B P R} (s : option { x : B & P x })
        (f : forall (x : B), P x -> option R) : option R :=
    match s with
    | Some s => unpack s f
    | None => None
    end.

Definition unpack_ty {P R} (ty : tydesc) (s : option { ty : tydesc & P ty })
        (f : P ty -> option R) : option R.
destruct s as [ s | ]; [ | exact None ].
destruct s as [ty' f'].
destruct (tydesc_eq_dec ty ty') as [Heq | _]; [ | exact None ].
rewrite Heq in f. exact (f f').
Defined.

Definition pack_denot t (f : state_fn (ty_denote t)) : option denotation :=
    Some (existT _ t f).

Definition pack_denot_list t (f : state_fn (list (ty_denote t))) : option denotation_list :=
    Some (existT _ t f).

Definition denote' : expr A n -> option denotation.
simple refine (
    let fix go (e : expr A n) : option denotation :=
        let fix go_list (es : list (expr A n)) : option denotation_list :=
            _ in
        _ in go
).

refine (
    match es with
    | [] => None
    | [e] =>
            unpack_opt (go e) (fun ty f =>
            pack_denot_list ty (fun sv sx =>
                let '(sv, sx, x) := f sv sx in
                (sv, sx, [x])))
    | e :: es =>
            unpack_opt (go e) (fun ty f =>
            unpack_opt (go_list es) (fun ty' f' =>
            match tydesc_eq_dec ty ty' with
            | left Heq =>
                    pack_denot_list ty (fun sv sx =>
                    let '(sv, sx, x) := f sv sx in
                    let '(sv, sx, x') := f' sv sx in
                    (sv, sx, _))
            | right _ => None
            end))
    end
).
  { rewrite <- Heq in x'. exact (x :: x'). }

refine (
    match e with
    | EVar i => pack_denot var_ty (fun sv sx => (sv, sx, sv !! i))
    | EXVar i => pack_denot xvar_ty (fun sv sx => (sv, sx, sx !! i))
    | ELit l =>
            unpack (convert_lit l) (fun xty xv =>
            pack_denot xty (fun sv sx => (sv, sx, xv)))
    | EUnary op xe =>
            unpack_opt (go xe) (fun xty xf =>
            unpack_opt (unop_denote op xty) (fun rty opf =>
            pack_denot rty (fun sv sx =>
                let '(sv, sx, x) := xf sv sx in
                (sv, sx, opf x))))
    | EBinary op xe ye =>
            unpack_opt (go xe) (fun xty xf =>
            unpack_opt (go ye) (fun yty yf =>
            unpack_opt (binop_denote op xty yty) (fun rty opf =>
            pack_denot rty (fun sv sx =>
                let '(sv, sx, x) := xf sv sx in
                let '(sv, sx, y) := yf sv sx in
                (sv, sx, opf x y)))))
    | EVarary op xes =>
            unpack_opt (go_list xes) (fun xty xf =>
            unpack_opt (varop_denote op xty) (fun rty opf =>
            pack_denot rty (fun sv sx =>
                let '(sv, sx, xs) := xf sv sx in
                (sv, sx, opf xs))))
    | EAssign i xe =>
            unpack_ty var_ty (go xe) (fun xf =>
            pack_denot nil_ty (fun sv sx =>
                let '(sv, sx, x) := xf sv sx in
                (multi_set sv i x, sx, nil)))
    | EXAssign i xe =>
            unpack_ty xvar_ty (go xe) (fun xf =>
            pack_denot nil_ty (fun sv sx =>
                let '(sv, sx, x) := xf sv sx in
                (sv, multi_set sx i x, nil)))
    | ECond ce xe ye =>
            unpack_opt (go ce) (fun cty cf =>
            unpack_opt (go xe) (fun xty xf =>
            unpack_opt (go ye) (fun yty yf =>
            unpack_opt (ternop_denote Cond cty xty yty) (fun rty opf =>
            pack_denot rty (fun sv sx =>
                (* Note: this implementation evaluates both sides.  It's
                   correct only when `xe` and `ye` have no side effects. *)
                let '(sv, sx, c) := cf sv sx in
                let '(sv, sx, x) := xf sv sx in
                let '(sv, sx, y) := yf sv sx in
                (sv, sx, opf c x y))))))
    | ESeq xe ye =>
            unpack_opt (go xe) (fun xt xf =>
            unpack_opt (go ye) (fun yt yf =>
            if tydesc_eq_dec xt nil_ty then
                pack_denot yt (fun sv sx =>
                    let '(sv, sx, _) := xf sv sx in
                    let '(sv, sx, y) := yf sv sx in
                    (sv, sx, y))
            else if tydesc_eq_dec yt nil_ty then
                pack_denot xt (fun sv sx =>
                    let '(sv, sx, x) := xf sv sx in
                    let '(sv, sx, _) := yf sv sx in
                    (sv, sx, x))
            else
                None (* both sides prdouced values - not allowed *)
            ))
    end
).
Defined.

Definition denote'_list : list (expr A n) -> option denotation_list.
simple refine (
    let go : expr A n -> option denotation := denote' in
    let fix go_list (es : list (expr A n)) : option denotation_list :=
        _ in go_list
).

refine (
    match es with
    | [] => None
    | [e] =>
            unpack_opt (go e) (fun ty f =>
            pack_denot_list ty (fun sv sx =>
                let '(sv, sx, x) := f sv sx in
                (sv, sx, [x])))
    | e :: es =>
            unpack_opt (go e) (fun ty f =>
            unpack_opt (go_list es) (fun ty' f' =>
            match tydesc_eq_dec ty ty' with
            | left Heq =>
                    pack_denot_list ty (fun sv sx =>
                    let '(sv, sx, x) := f sv sx in
                    let '(sv, sx, x') := f' sv sx in
                    (sv, sx, _))
            | right _ => None
            end))
    end
).
  { rewrite <- Heq in x'. exact (x :: x'). }
Defined.

End denote.

Require Import List.
Import ListNotations.
Require Import String.
Require Import Flocq.Appli.Fappli_IEEE_bits.
Require Import Flocq.Appli.Fappli_IEEE.
Require Import ZArith.

Require Import v1.Multi.
Require Import v1.NeutronTactics.
Require Import v1.FloatAux.
Require Import v1.Util.

Require Import epics.SpecTypes.
Require Import expr.Expr.
Require Import floatabs.Records.
Require Import floatabs.RecordData.



Local Open Scope Z_scope.

Definition check_overflow x0 x1 : abs_value :=
    if Z_le_gt_dec x0 (-2 ^ 52) then None
    else if Z_ge_lt_dec x1 (2 ^ 52) then None
    else Some (x0, x1).

Definition abs_opp (x : abs_value) : abs_value :=
    match x with
    | Some (x0, x1) => check_overflow (Z.opp x1) (Z.opp x0)
    | _ => None
    end.

Definition abs_plus (x y : abs_value) : abs_value :=
    match x, y with
    | Some (x0, x1), Some (y0, y1) => check_overflow (x0 + y0) (x1 + y1)
    | _, _ => None
    end.

Definition abs_minus (x y : abs_value) : abs_value :=
    match x, y with
    | Some (x0, x1), Some (y0, y1) => check_overflow (x0 - y1) (x1 - y0)
    | _, _ => None
    end.

Definition abs_mult (x y : abs_value) : abs_value :=
    match x, y with
    | Some (x0, x1), Some (y0, y1) =>
            let z0 := Z.min (Z.min (x0 * y0) (x0 * y1)) (Z.min (x1 * y0) (x1 * y1)) in
            let z1 := Z.max (Z.max (x0 * y0) (x0 * y1)) (Z.max (x1 * y0) (x1 * y1)) in
            check_overflow z0 z1
    | _, _ => None
    end.

Definition abs_join (x y : abs_value) : abs_value :=
    match x, y with
    | Some (x0, x1), Some (y0, y1) => check_overflow (Z.min x0 y0) (Z.max x1 y1)
    | _, _ => None
    end.

Definition abs_min (x y : abs_value) : abs_value :=
    match x, y with
    | Some (x0, x1), Some (y0, y1) => check_overflow (Z.min x0 y0) (Z.min x1 y1)
    | _, _ => None
    end.

Definition abs_max (x y : abs_value) : abs_value :=
    match x, y with
    | Some (x0, x1), Some (y0, y1) => check_overflow (Z.max x0 y0) (Z.max x1 y1)
    | _, _ => None
    end.

Fixpoint abs_minimum (xs : list abs_value) :=
    match xs with
    | [] => Some (0, 0)
    | x :: xs => abs_min x (abs_minimum xs)
    end.

Fixpoint abs_maximum (xs : list abs_value) :=
    match xs with
    | [] => Some (0, 0)
    | [x] => x
    | x :: xs => abs_max x (abs_maximum xs)
    end.



(*
Definition abs_eq (x y : e_double) :=
    match Bcompare _ _ x y with
    | Some Datatypes.Eq => one
    | _ => zero
    end.

Definition b64_ne (x y : e_double) :=
    match Bcompare _ _ x y with
    | Some Datatypes.Lt | Some Datatypes.Gt => one
    | _ => zero
    end.

Definition b64_lt (x y : e_double) :=
    match Bcompare _ _ x y with
    | Some Datatypes.Lt => one
    | _ => zero
    end.

Definition b64_le (x y : e_double) :=
    match Bcompare _ _ x y with
    | Some Datatypes.Lt | Some Datatypes.Eq => one
    | _ => zero
    end.

Definition b64_gt (x y : e_double) :=
    match Bcompare _ _ x y with
    | Some Datatypes.Gt => one
    | _ => zero
    end.

Definition b64_ge (x y : e_double) :=
    match Bcompare _ _ x y with
    | Some Datatypes.Gt | Some Datatypes.Eq => one
    | _ => zero
    end.

Definition b64_and (x y : e_double) :=
    if is_zero x then zero else (if is_zero y then zero else one).

Definition b64_or (x y : e_double) :=
    if is_zero x then (if is_zero y then zero else one) else one.
*)



Inductive abs_tydesc := Nil | Abs.
Scheme Equality for abs_tydesc.

Definition abs_ty_denote ty :=
    match ty with
    | Nil => unit
    | Abs => abs_value
    end.

Definition abs_bool : abs_value := Some (0, 1).

Definition double_abs (d : e_double) : abs_value :=
    match B2Z_safe d with
    | Some z => Some (z, z)
    | None => None
    end.

Definition abs_eval_bits : eval_bits e_double := 
    {| tydesc := abs_tydesc
    ; tydesc_eq_dec := abs_tydesc_eq_dec
    ; ty_denote := abs_ty_denote

    ; var_ty := Abs
    ; xvar_ty := Nil
    ; convert_lit := fun d => existT abs_ty_denote Abs (double_abs d)

    ; nil_ty := Nil
    ; nil_value := tt

    ; unop_denote := fun op ty1 =>
        match ty1 with
        | Abs =>
                let mk f := Some (existT (unop_impl _ Abs) Abs f) in
                match op with
                | NotAlg => mk abs_opp
                | NotLog => mk (fun _ => abs_bool)
                end
        | Nil => None
        end

    ; binop_denote := fun op ty1 ty2 =>
        match ty1, ty2 with
        | Abs, Abs =>
                let mk f := Some (existT (binop_impl _ Abs Abs) Abs f) in
                match op with
                | Add => mk abs_plus
                | Sub => mk abs_minus
                | Mul => mk abs_mult
                | Div => mk (fun _ _ => None)
                | Ge => mk (fun _ _ => abs_bool)
                | Gt => mk (fun _ _ => abs_bool)
                | Le => mk (fun _ _ => abs_bool)
                | Lt => mk (fun _ _ => abs_bool)
                | Ne => mk (fun _ _ => abs_bool)
                | Eq => mk (fun _ _ => abs_bool)
                | AndLog => mk (fun _ _ => abs_bool)
                | OrLog => mk (fun _ _ => abs_bool)
                end
        | _, _ => None
        end

    ; ternop_denote := fun op ty1 ty2 ty3 =>
        match ty1, ty2, ty3 with
        | Abs, Abs, Abs =>
                let mk f := Some (existT (ternop_impl _ Abs Abs Abs) Abs f) in
                match op with
                | Cond => mk (fun _ x y => abs_join x y)
                end
        | _, _, _ => None
        end

    ; varop_denote := fun op ty1 =>
        match ty1 with
        | Abs =>
                let mk f := Some (existT (varop_impl _ Abs) Abs f) in
                match op with
                | Min => mk (fun xs => abs_minimum xs)
                | Max => mk (fun xs => abs_maximum xs)
                end
        | _ => None
        end
    |}.

Definition denote {n} (e : expr e_double n) :
        option (multi n abs_value -> multi n abs_value * abs_value) :=
    unpack_ty abs_eval_bits Abs (denote' abs_eval_bits e)
        (fun f =>
            let f' sv :=
                let '(sv, sx, r) := f sv (multi_rep n tt) in
                (sv, r) in
            Some f').


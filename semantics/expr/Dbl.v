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



Definition b64_eq (x y : e_double) :=
    match Bcompare _ _ x y with
    | Some Datatypes.Eq => d_one
    | _ => d_zero
    end.

Definition b64_ne (x y : e_double) :=
    match Bcompare _ _ x y with
    | Some Datatypes.Lt | Some Datatypes.Gt => d_one
    | _ => d_zero
    end.

Definition b64_lt (x y : e_double) :=
    match Bcompare _ _ x y with
    | Some Datatypes.Lt => d_one
    | _ => d_zero
    end.

Definition b64_le (x y : e_double) :=
    match Bcompare _ _ x y with
    | Some Datatypes.Lt | Some Datatypes.Eq => d_one
    | _ => d_zero
    end.

Definition b64_gt (x y : e_double) :=
    match Bcompare _ _ x y with
    | Some Datatypes.Gt => d_one
    | _ => d_zero
    end.

Definition b64_ge (x y : e_double) :=
    match Bcompare _ _ x y with
    | Some Datatypes.Gt | Some Datatypes.Eq => d_one
    | _ => d_zero
    end.

Definition b64_and (x y : e_double) :=
    if e_double_eq_dec x d_zero then d_zero
    else if e_double_eq_dec y d_zero then d_zero
    else d_one.

Definition b64_or (x y : e_double) :=
    if e_double_eq_dec x d_zero then
        (if e_double_eq_dec y d_zero then d_zero
         else d_one)
    else d_one.


Definition b64_min (x y : e_double) :=
    match Bcompare _ _ x y with
    | Some Datatypes.Lt => x
    | _ => y
    end.

Definition b64_max (x y : e_double) :=
    match Bcompare _ _ x y with
    | Some Datatypes.Lt => y
    | _ => x
    end.

Fixpoint b64_minimum (xs : list e_double) :=
    match xs with
    | [] => d_zero
    | x :: xs => b64_min x (b64_minimum xs)
    end.

Fixpoint b64_maximum (xs : list e_double) :=
    match xs with
    | [] => d_zero
    | [x] => x
    | x :: xs => b64_max x (b64_maximum xs)
    end.



Inductive dbl_tydesc := Nil | Dbl.
Scheme Equality for dbl_tydesc.

Definition dbl_ty_denote ty :=
    match ty with
    | Nil => unit
    | Dbl => e_double
    end.

Definition dbl_eval_bits : eval_bits e_double := 
    {| tydesc := dbl_tydesc
    ; tydesc_eq_dec := dbl_tydesc_eq_dec
    ; ty_denote := dbl_ty_denote

    ; var_ty := Dbl
    ; xvar_ty := Nil
    ; convert_lit := fun d => existT dbl_ty_denote Dbl d

    ; nil_ty := Nil
    ; nil_value := tt

    ; unop_denote := fun op ty1 =>
        match ty1 with
        | Dbl =>
                let mk f := Some (existT (unop_impl _ Dbl) Dbl f) in
                match op with
                | NotAlg => mk (fun x => b64_opp x)
                | NotLog => mk (fun x =>
                        if e_double_eq_dec x d_zero then d_one else d_zero)
                end
        | Nil => None
        end

    ; binop_denote := fun op ty1 ty2 =>
        match ty1, ty2 with
        | Dbl, Dbl =>
                let mk f := Some (existT (binop_impl _ Dbl Dbl) Dbl f) in
                match op with
                | Add => mk (b64_plus mode_NE)
                | Sub => mk (b64_minus mode_NE)
                | Mul => mk (b64_mult mode_NE)
                | Div => mk (b64_div mode_NE)
                | Ge => mk b64_ge
                | Gt => mk b64_gt
                | Le => mk b64_le
                | Lt => mk b64_lt
                | Ne => mk b64_ne
                | Eq => mk b64_eq
                | AndLog => mk b64_and
                | OrLog => mk b64_or
                end
        | _, _ => None
        end

    ; ternop_denote := fun op ty1 ty2 ty3 =>
        match ty1, ty2, ty3 with
        | Dbl, Dbl, Dbl =>
                let mk f := Some (existT (ternop_impl _ Dbl Dbl Dbl) Dbl f) in
                match op with
                | Cond => mk (fun c x y =>
                        if e_double_eq_dec c d_zero then y else x)
                end
        | _, _, _ => None
        end

    ; varop_denote := fun op ty1 =>
        match ty1 with
        | Dbl =>
                let mk f := Some (existT (varop_impl _ Dbl) Dbl f) in
                match op with
                | Min => mk (fun xs => b64_minimum xs)
                | Max => mk (fun xs => b64_maximum xs)
                end
        | _ => None
        end
    |}.

Definition denote {n} (e : expr e_double n) :
        option (multi n e_double -> multi n e_double * e_double) :=
    unpack_ty dbl_eval_bits Dbl (denote' dbl_eval_bits e)
        (fun f =>
            let f' sv :=
                let '(sv, sx, r) := f sv (multi_rep n tt) in
                (sv, r) in
            Some f').


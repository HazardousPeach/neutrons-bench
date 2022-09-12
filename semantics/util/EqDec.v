Require Import Arith.
Require Import List.
Require Import ZArith.


Structure DecidableEquality :=
    { dec_eq_type :> Set
    ; dec_eq_decide : forall (x y : dec_eq_type), { x = y } + { x <> y }
    }.

Arguments Build_DecidableEquality [_] _.

Definition eq_dec {A : DecidableEquality} (x y : A) : { x = y } + { x <> y } :=
    dec_eq_decide A x y.
Hint Resolve eq_dec : eq_dec.


Canonical Structure dec_eq_nat :=
    Build_DecidableEquality eq_nat_dec.

Canonical Structure dec_eq_Z :=
    Build_DecidableEquality Z.eq_dec.

Canonical Structure dec_eq_list (A : DecidableEquality) :=
    Build_DecidableEquality (list_eq_dec (@eq_dec A)).

Definition prod_eq_dec {A B}
        (A_eq_dec : forall (x y : A), { x = y } + { x <> y })
        (B_eq_dec : forall (x y : B), { x = y } + { x <> y })
        (x y : A * B) : { x = y } + { x <> y } :=
    ltac:(decide equality).

Canonical Structure dec_eq_prod (A B : DecidableEquality) :=
    @Build_DecidableEquality _ (prod_eq_dec (@eq_dec A) (@eq_dec B)).



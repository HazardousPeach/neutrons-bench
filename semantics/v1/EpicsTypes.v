Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import String.
Require Import Flocq.Appli.Fappli_IEEE.
Require Import Flocq.Appli.Fappli_IEEE_bits.

Require Import v1.Multi.
Require Import v1.Util.
Require Import v1.NeutronTactics.
Require Import v1.FloatAux.

Require Import ProofIrrelevance.

Set Implicit Arguments.


Definition record_name := nat.


Definition e_double := binary64.

Definition is_zero (x : e_double) : bool :=
    match x with
    | B754_zero _ _ _ => true
    | _ => false
    end.

Definition zero : e_double := Z2B64 0.
Definition one : e_double := Z2B64 1.

Lemma proj1_sig_eq : forall A P (x y : { x : A | P x }),
        proj1_sig x = proj1_sig y ->
        x = y.
intros0 Heq.
destruct x, y. simpl in *.
subst x0. replace p0 with p by (eapply proof_irrelevance).
reflexivity.
Qed.

Definition e_double_eq_dec (x y : e_double) : { x = y } + { x <> y }.
destruct x, y; try solve [right; discriminate].

- destruct (Bool.bool_dec b b0); [ left | right ]; congruence.
- destruct (Bool.bool_dec b b0); [ left | right ]; congruence.
- unfold nan_pl in *.
  destruct (Bool.bool_dec b b0); [ | right; congruence ].
  destruct (Pos.eq_dec (proj1_sig n) (proj1_sig n0)); [ | right; congruence ].
  forward eapply proj1_sig_eq. { exact e0. }
  subst. left. reflexivity.
- destruct (Bool.bool_dec b b0); [ | right; congruence ].
  destruct (Pos.eq_dec m m0); [ | right; congruence ].
  destruct (Z.eq_dec e e1); [ | right; inversion 1; congruence ].
  subst. left. f_equal. eapply proof_irrelevance.
Defined.


Definition e_string := string.


Inductive e_enum (max : Z) :=
| EEnum (val : Z) (Hlt : (val < max)%Z).
Implicit Arguments EEnum [].
Ltac mk_enum x := eapply (@EEnum x); omega.
Definition enum_val max (e : e_enum max) :=
    match e with
    | EEnum _ val _ => val
    end.

Definition e_enum_eq_dec (max : Z) (x y : e_enum max) : { x = y } + { x <> y }.
destruct x, y; try solve [right; discriminate].
destruct (Z.eq_dec val val0); [ | right; congruence ].
subst. left. f_equal. eapply proof_irrelevance.
Defined.


Definition LONG_MAX := (2^31)%Z.

Inductive e_long :=
| ELong (val : Z) (Hrange : (-LONG_MAX <= val < LONG_MAX)%Z).
Implicit Arguments ELong [].

Ltac mk_long x := eapply (@ELong x); omega.

Definition long_val (l : e_long) :=
    match l with
    | ELong val _ => val
    end.

Definition e_long_eq_dec (x y : e_long) : { x = y } + { x <> y }.
destruct x, y; try solve [right; discriminate].
destruct (Z.eq_dec val val0); [ | right; congruence ].
subst. left. f_equal. eapply proof_irrelevance.
Defined.


Inductive elem_type :=
| TeDouble
| TeString
| TeLong
.

Definition elem_type_eq_dec (a b : elem_type) : { a = b } + { a <> b } :=
    ltac:(decide equality).

Definition elem_type_denote t :=
    match t with
    | TeDouble => e_double
    | TeString => e_string
    | TeLong => e_long
    end.

Definition e_array ty n := multi n (elem_type_denote ty).

Definition e_array_eq_dec' ty n (x y : multi' n (elem_type_denote ty)) : { x = y } + { x <> y }.
generalize dependent n. induction n; simpl; intros.
- destruct ty; eauto using e_double_eq_dec, string_dec, e_long_eq_dec.
- destruct x, y.
  destruct (IHn m m0); [ subst | right; congruence ].
  destruct ty; simpl in *.
  + destruct (e_double_eq_dec e e0); [ subst | right; congruence ]. eauto.
  + destruct (string_dec e e0); [ subst | right; congruence ]. eauto.
  + destruct (e_long_eq_dec e e0); [ subst | right; congruence ]. eauto.
Defined.

Definition e_array_eq_dec ty n (x y : e_array ty n) : { x = y } + { x <> y }.
unfold e_array in *.
generalize dependent n. induction n; simpl; intros.
- destruct x, y. eauto.
- destruct (e_array_eq_dec' ty n x y); eauto.
Qed.

Definition default_array ty n : e_array ty n.
refine (
    match ty as ty_ return e_array ty_ n with
    | TeDouble => multi_rep n zero
    | TeString => multi_rep n EmptyString
    | TeLong => multi_rep n (ELong 0%Z _)
    end).
- hide. unfold LONG_MAX.
  assert (0 < 2^31)%Z.  { eapply Z.pow_pos_nonneg; omega. }
  omega.
Defined.




Inductive field_type :=
| TDouble
| TString
| TEnum (max : Z)
| TLong
| TArray (elem : elem_type) (size : nat)
.

Definition field_type_eq_dec (a b : field_type) : { a = b } + { a <> b }.
decide equality;
eauto using Z_eq_dec, eq_nat_dec, elem_type_eq_dec.
Defined.


Inductive field_type_matcher :=
| MatchExact (ft : field_type)
| MatchAnyNumeric.

Definition check_match_for_type (m : field_type_matcher) (ft : field_type) : bool :=
    match m with
    | MatchExact ft' => if field_type_eq_dec ft ft' then true else false
    | MatchAnyNumeric =>
            match ft with
            | TDouble => true
            | TString => false
            | TEnum _ => true
            | TLong => true
            | TArray _ _ => false
            end
    end.

Fixpoint find_match_for_type {A} (ms : list (field_type_matcher * A)) (ft : field_type) : option A :=
    match ms with
    | [] => None
    | (m, x) :: ms =>
            if check_match_for_type m ft then Some x else find_match_for_type ms ft
    end.



Inductive value : Set :=
| VDouble : e_double -> value
| VString : e_string -> value
| VEnum {max : Z} : e_enum max -> value
| VLong : e_long -> value
| VArray {elem : elem_type} {size : nat} : e_array elem size -> value
.

Definition value_eq_dec (x y : value) : { x = y } + { x <> y }.
destruct x, y; try solve [right; discriminate].
- destruct (e_double_eq_dec e e0); [ left | right ]; congruence.
- destruct (string_dec e e0); [ left | right ]; congruence.
- destruct (Z.eq_dec max max0); [ subst | right; congruence ].
  destruct (e_enum_eq_dec e e0); [ left; congruence | right; inversion 1 ].
  forward eapply inj_pair2; eauto.
- destruct (e_long_eq_dec e e0); [ left | right ]; congruence.
- destruct (elem_type_eq_dec elem elem0); [ subst | right; congruence ].
  destruct (eq_nat_dec size size0); [ subst | right; congruence ].
  destruct (e_array_eq_dec _ _ e e0); [ left; congruence | right; inversion 1 ].
  forward eapply inj_pair2 with (1 := **); eauto.
  forward eapply inj_pair2 with (1 := **); eauto.
Defined.


Definition value_type v :=
    match v with
    | VDouble _ => TDouble
    | VString _ => TString
    | @VEnum max _ => TEnum max
    | VLong _ => TLong
    | @VArray elem size _ => TArray elem size
    end.


Definition unwrap_double (v : value) : option e_double :=
    match v with
    | VDouble x => Some x
    | _ => None
    end.

Definition unwrap_string (v : value) : option e_string :=
    match v with
    | VString x => Some x
    | _ => None
    end.

Definition unwrap_enum (max : Z) (v : value) : option (e_enum max) :=
    match v with
    | @VEnum max' x =>
            if Z.eq_dec max max' then Some ltac:(subst max; exact x) else None
    | _ => None
    end.

Definition unwrap_long (v : value) : option e_long :=
    match v with
    | VLong x => Some x
    | _ => None
    end.

Definition unwrap_array (elem : elem_type) (size : nat) (v : value) : option (e_array elem size) :=
    match v with
    | @VArray elem' size' x =>
            if elem_type_eq_dec elem elem' then
                if eq_nat_dec size size' then
                    Some ltac:(subst; exact x)
                else None
            else None
    | _ => None
    end.

Inductive field_name : Set :=
| f_VAL : field_name
| f_PVAL : field_name
| f_OVAL : field_name
| f_SVAL : field_name
| f_OSV : field_name
| f_AVAL : field_name
| f_OAV : field_name
| f_A_to_L : index 12 -> field_name
| f_AA_to_LL : index 12 -> field_name
| f_DO1_to_DOA : index 10 -> field_name
| f_PACT : field_name
| f_PROC : field_name

| f_tmp : nat -> field_name
.

Definition field_name_eq_dec (x y : field_name) : { x = y } + { x <> y }.
destruct x, y; try solve [left; reflexivity | right; discriminate].
all: try (destruct (index_eq_dec _ i i0); [ left | right ]; congruence).
all: try (destruct (Nat.eq_dec n n0); [ left | right ]; congruence).
Defined.

Inductive process_passive_flag : Set := PP | NPP.
Definition process_passive_flag_eq_dec (a b : process_passive_flag) : { a = b } + { a <> b } :=
    ltac:(decide equality).


Record field_link : Set :=
    FieldLink {
        fl_rn : record_name;
        fl_fn : field_name;
        fl_pp : process_passive_flag
    }.

Record record_link : Set :=
    RecordLink {
        rl_rn : record_name
    }.

Inductive in_link :=
| InLinkNull
| InLinkConstant (x : e_double)
| InLinkField (fl : field_link)
(* | InLinkHardware ??? *)
.

Inductive out_link :=
| OutLinkNull
| OutLinkField (fl : field_link)
(* | InLinkHardware ??? *)
.

Inductive fwd_link :=
| FwdLinkNull
| FwdLinkRecord (rl : record_link)
.


(* misc. utilities *)

Definition lookup A : list A -> record_name -> option A := @nth_error A.

Fixpoint map_opt A B (f : A -> option B) (xs : list A) : option (list B) :=
    match xs with
    | [] => Some []
    | x :: xs =>
            f x >>= fun y =>
            map_opt f xs >>= fun ys =>
            Some (y :: ys)
    end.



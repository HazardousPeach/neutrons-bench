Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import String.
Require Import Flocq.Appli.Fappli_IEEE.
Require Import Flocq.Appli.Fappli_IEEE_bits.
Require Import ProofIrrelevance.

Require Import v1.Multi.
Require Import v1.Util.
Require Import v1.NeutronTactics.
Require v1.FloatAux. (* for Z2B64 *)

Local Open Scope Z.





Definition record_name := nat.

Inductive field_name :=
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

| f_tmp0 : field_name
.



Inductive elem_type :=
| TeDouble
| TeLong.

Inductive field_type :=
| TDouble
| TString
| TEnum
| TLong
| TArray (ty : elem_type) (n : nat).

Definition elem_type_eq_dec (a b : elem_type) : { a = b } + { a <> b } :=
    ltac:(decide equality).

Definition field_type_eq_dec (a b : field_type) : { a = b } + { a <> b }.
decide equality;
eauto using Z_eq_dec, eq_nat_dec, elem_type_eq_dec.
Defined.



Definition e_double := binary64.

Definition d_zero : e_double := FloatAux.Z2B64 0.
Definition d_one : e_double := FloatAux.Z2B64 1.

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

(* Note this is NOT equivalent to `e_double_eq_dec`, as it uses proper floating
   point comparison, in which `+0 == -0` (among other things). *)
Definition e_double_is_eq (x y : e_double) :=
    match Bcompare _ _ x y with
    | Some Datatypes.Eq => true
    | _ => false
    end.



Definition e_string := string.

Definition e_string_eq_dec := string_dec.



Definition ENUM_MAX := (2^16)%Z.

Inductive e_enum :=
| EEnum (val : Z) (pf : 0 <= val < ENUM_MAX).

Definition e_enum_eq_dec (x y : e_enum) : { x = y } + { x <> y }.
destruct x, y; try solve [right; discriminate].
destruct (Z.eq_dec val val0); [ | right; congruence ].
subst. left. f_equal. eapply proof_irrelevance.
Defined.

Definition enum_val e :=
    match e with
    | EEnum z _ => z
    end.

Definition e_zero : e_enum.
refine (EEnum 0 _).
hide. compute. split; congruence.
Defined.



Definition LONG_MAX := (2^31)%Z.

Inductive e_long :=
| ELong (val : Z) (pf : -LONG_MAX <= val < LONG_MAX).

Definition e_long_eq_dec (x y : e_long) : { x = y } + { x <> y }.
destruct x, y; try solve [right; discriminate].
destruct (Z.eq_dec val val0); [ | right; congruence ].
subst. left. f_equal. eapply proof_irrelevance.
Defined.

Definition long_val e :=
    match e with
    | ELong z _ => z
    end.

Definition l_zero : e_long.
refine (ELong 0 _).
hide. compute. split; congruence.
Defined.



Definition elem_type_denote t :=
    match t with
    | TeDouble => e_double
    | TeLong => e_long
    end.

Definition e_array ty n := multi n (elem_type_denote ty).

Definition default_array ty n : e_array ty n.
refine (
    match ty as ty_ return e_array ty_ n with
    | TeDouble => multi_rep n d_zero
    | TeLong => multi_rep n (ELong 0%Z _)
    end).
- hide. unfold LONG_MAX.
  assert (0 < 2^31)%Z.  { eapply Z.pow_pos_nonneg; omega. }
  omega.
Defined.



(* Generic values *)

Inductive value : Set :=
| VDouble : e_double -> value
| VString : e_string -> value
| VEnum : e_enum -> value
| VLong : e_long -> value
| VArray {ty : elem_type} {n : nat} : e_array ty n -> value
.

Definition value_type v :=
    match v with
    | VDouble _ => TDouble
    | VString _ => TString
    | VEnum _ => TEnum
    | VLong _ => TLong
    | @VArray elem size _ => TArray elem size
    end.


(* `value` downcasts *)

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

Definition unwrap_enum (v : value) : option e_enum :=
    match v with
    | VEnum x => Some x
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



(* Matchers for finding an item with a particular type.  This is used for
   s/acalcout records, where the field sent to the output link depends on the
   type of the target of the link. *)

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
            | TEnum => true
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



(* Record and field links *)

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

Definition lookup {A} : list A -> record_name -> option A := @nth_error A.

Fixpoint map_opt {A B} (f : A -> option B) (xs : list A) : option (list B) :=
    match xs with
    | [] => Some []
    | x :: xs =>
            f x >>= fun y =>
            map_opt f xs >>= fun ys =>
            Some (y :: ys)
    end.



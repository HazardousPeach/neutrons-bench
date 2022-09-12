Require Import List.
Import ListNotations.

Require Export epics.SpecTypes.

Require Import v1.Multi.
Require Import v1.MultiAux.
Require Import v1.NeutronTactics.
Require Import util.EqDec.


Definition field_name_eq_dec (x y : field_name) : { x = y } + { x <> y }.
decide equality; auto using index_eq_dec.
Defined.

Canonical Structure dec_eq_field_name :=
    Build_DecidableEquality field_name_eq_dec.


Canonical Structure dec_eq_elem_type :=
    Build_DecidableEquality elem_type_eq_dec.

Canonical Structure dec_eq_field_type :=
    Build_DecidableEquality field_type_eq_dec.

Canonical Structure dec_eq_e_double :=
    Build_DecidableEquality e_double_eq_dec.

Canonical Structure dec_eq_e_string :=
    Build_DecidableEquality e_string_eq_dec.

Canonical Structure dec_eq_e_enum :=
    Build_DecidableEquality e_enum_eq_dec.

Canonical Structure dec_eq_e_long :=
    Build_DecidableEquality e_long_eq_dec.

Definition e_array_eq_dec {ty n} (x y : e_array ty n) : { x = y } + { x <> y }.
destruct ty; apply multi_eq_dec; eauto using eq_dec.
Defined.

Canonical Structure dec_eq_e_array ty n :=
    Build_DecidableEquality (@e_array_eq_dec ty n).

Canonical Structure dec_eq_process_passive_flag :=
    Build_DecidableEquality process_passive_flag_eq_dec.


Definition value_eq_dec (x y : value) : { x = y } + { x <> y }.
destruct x, y; try solve [right; inversion 1].
- destruct (eq_dec e e0); left + right; congruence.
- destruct (eq_dec e e0); left + right; congruence.
- destruct (eq_dec e e0); left + right; congruence.
- destruct (eq_dec e e0); left + right; congruence.
- destruct (eq_dec ty ty0); try (right; congruence).  subst ty0.
  destruct (eq_dec n n0); try (right; congruence).  subst n0.
  destruct (eq_dec e e0).
  + left. congruence.
  + right. inversion 1. fix_existT; eauto using eq_dec.
Defined.

Canonical Structure dec_eq_value :=
    Build_DecidableEquality value_eq_dec.


Definition all_field_names :=
    [ f_VAL; f_PVAL;  f_OVAL; f_SVAL; f_OSV; f_AVAL; f_OAV
    ; f_PACT; f_PROC; f_tmp0 ] ++
    map f_A_to_L (index_list 12) ++
    map f_AA_to_LL (index_list 12) ++
    map f_DO1_to_DOA (index_list 10).

Lemma all_field_names_complete : forall fn, In fn all_field_names.
destruct fn.
all: unfold all_field_names.
all: try solve [rewrite in_app_iff; left; simpl; eauto 99].
all: rewrite in_app_iff; right.

- (* f_A_to_L *)
  rewrite in_app_iff. left.
  eapply in_map, index_list_in.

- (* f_AA_to_LL *)
  rewrite 2 in_app_iff. right. left.
  eapply in_map, index_list_in.

- (* f_DO1_to_DOA *)
  rewrite 2 in_app_iff. right. right.
  eapply in_map, index_list_in.
Qed.

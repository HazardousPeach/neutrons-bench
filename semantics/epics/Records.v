Require Import String.
Require Import ZArith.
Require Import Omega.

Require Export epics.SpecRecords.
Require Export epics.SpecRecordData.
Require Export epics.SpecRecordSetters.
Require Export epics.SpecTypes.

Require Import epics.Types.
Require Import util.EqDec.
Require Import v1.Multi.
Require Import v1.NeutronTactics.

Tactic Notation "destruct_record" constr(r) "as" "[" ident(x) "]" :=
    destruct r as [
        x | x | x | (* acalcout*) ?n x | x |
        x | x | x | x | x |
        x | x | x | x | x |
        x | (* waveform *) ?ty ?n x | (* subArray *) ?ty ?n ?m x | x
    ].

Tactic Notation "destruct_record" constr(r) "as" "[" ident(x) ident(y) "]" :=
    destruct r as [
        x y | x y | x y | (* acalcout*) ?n x y | x y |
        x y | x y | x y | x y | x y |
        x y | x y | x y | x y | x y |
        x y | (* waveform *) ?ty ?n x y | (* subArray *) ?ty ?n ?m x y | x y
    ].

Tactic Notation "destruct_record" constr(r) := destruct_record r as [c s].


Canonical Structure dec_eq_record_type :=
    Build_DecidableEquality record_type_eq_dec.


Definition eq_dec_injective {A B} (f : A -> B)
    (Hinj : forall x y, f x = f y -> x = y)
    (eq_dec : forall (x y : A), { x = y } + { x <> y })
    (x y : A) :
    { f x = f y } + { f x <> f y }.
destruct (eq_dec x y).
- left. congruence.
- right. intro. eauto.
Defined.

Ltac decide_equality_with_epics_types :=
    decide equality; eauto using eq_dec, multi_eq_dec.

Definition record_state_eq_dec (x y : record_state) : { x = y } + { x <> y }.
destruct x.
all: destruct y; try solve [right; discriminate].
all: try (
    eapply eq_dec_injective;
    [ intros; congruence
    | decide_equality_with_epics_types ]
).

- (* ArrayCalcOut *)
  destruct (eq_nat_dec n n0); cycle 1.
    { right. congruence. }
  subst.  eapply eq_dec_injective.
  + intros. inversion H. fix_existT. auto.
  + decide_equality_with_epics_types.

- (* Waveform *)
  destruct (eq_nat_dec n n0); cycle 1.
    { right. congruence. }
  destruct (elem_type_eq_dec ty ty0); cycle 1.
    { right. congruence. }

  subst.  eapply eq_dec_injective.
  + intros. inversion H. fix_existT. auto.
  + decide_equality_with_epics_types.

- (* Subarray *)
  destruct (eq_nat_dec n n0); cycle 1.
    { right. congruence. }
  destruct (eq_nat_dec m m0); cycle 1.
    { right. congruence. }
  destruct (elem_type_eq_dec ty ty0); cycle 1.
    { right. congruence. }

  subst.  eapply eq_dec_injective.
  + intros. inversion H. fix_existT. auto.
  + decide_equality_with_epics_types.
Defined.

Canonical Structure dec_eq_record_state :=
    Build_DecidableEquality record_state_eq_dec.


Definition default_record (rt : record_type) : record_state :=
    match rt with
    | RtCalc => RsCalc (CalcState
            (multi_rep _ d_zero) d_zero)
    | RtCalcOut => RsCalcOut (CalcOutState
            (multi_rep _ d_zero) d_zero d_zero d_zero d_zero)
    | RtStrCalcOut => RsStrCalcOut (StrCalcOutState
            (multi_rep _ d_zero) (multi_rep _ EmptyString)
            d_zero EmptyString d_zero d_zero EmptyString d_zero)
    | RtArrayCalcOut n => RsArrayCalcOut n (ArrayCalcOutState n
            (multi_rep _ d_zero) (multi_rep _ (multi_rep _ d_zero))
            d_zero (multi_rep _ d_zero) d_zero d_zero (multi_rep _ d_zero) d_zero)
    | RtFanout => RsFanout (FanoutState)
    | RtDFanout => RsDFanout (DFanoutState d_zero)
    | RtSeq => RsSeq (SeqState
            (multi_rep _ d_zero) (EEnum 0 ltac:(hide; compute; split; congruence)))
    | RtAnalogIn => RsAnalogIn (AnalogInState d_zero)
    | RtAnalogOut => RsAnalogOut (AnalogOutState d_zero d_zero)
    | RtBinaryIn => RsBinaryIn (BinaryInState
            (EEnum 0 ltac:(hide; compute; split; congruence)))
    | RtBinaryOut => RsBinaryOut (BinaryOutState
            (EEnum 0 ltac:(hide; compute; split; congruence)))
    | RtMBBO => RsMBBO (MBBOState
            (EEnum 0 ltac:(hide; compute; split; congruence)))
    | RtStringIn => RsStringIn (StringInState EmptyString)
    | RtStringOut => RsStringOut (StringOutState EmptyString)
    | RtLongIn => RsLongIn (LongInState l_zero)
    | RtLongOut => RsLongOut (LongOutState l_zero)
    | RtWaveform ty n => RsWaveform ty n (WaveformState ty n
            (default_array ty n))
    | RtSubarray ty n m => RsSubarray ty n m (SubarrayState ty n m
            (default_array ty n) (default_array ty m))
    | RtAsyn => RsAsyn (AsynState)
    end.

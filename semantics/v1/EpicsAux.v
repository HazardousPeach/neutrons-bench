Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Omega.

Require Import v1.NeutronTactics.
Require Import v1.Util.

Set Default Timeout 10.
Set Implicit Arguments.



Ltac unmangle_process :=
  repeat match goal with
  | [ x := ?_x : ?T |- _ ] =>
          subst x;
          rename _x into x
  end;
  repeat match goal with
  | [ x := ?_x : _ |- _ ] =>
          subst x
  end.

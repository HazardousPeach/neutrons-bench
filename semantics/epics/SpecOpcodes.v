Require Import ZArith.

Require Import expr.Expr.
Require Import epics.SpecRecords.
Require Import epics.SpecRecordData.
Require Import epics.SpecTypes.


(* Untyped micro-operation.  Used only as an intermediate value during database compilation *)
Inductive umicro : Set :=
| USetConst (fn : field_name) (val : value)
| UCopy (fn_src : field_name) (fn_dest : field_name)
| UReadLink (il : field_link) (fn : field_name)
| UWriteLink (fn : field_name) (ol : field_link)
(* Choose a local field based on the type of the output link, and write its value.
   Note that this `umicro` variant has no `micro` equivalent - see the comment
   in type_umicro for details. *)
| UWriteLinkTyped (fns : list (field_type_matcher * field_name)) (ol : field_link)
| UProcess (fl : record_link)
| UCalculate (expr : expr e_double 12) (fn_out : field_name)
        (*
| UCalculateStr
        (expr : expr (e_double + e_string) 12)
        (fn_out_dbl : field_name)
        (fn_out_str : field_name)
        *)
| UHwRead (fn : field_name)
| UHwWrite (fn : field_name) (out_ty : field_type)
| UCalcCond (fn_cur : field_name) (fn_prev : field_name) (oopt : output_exec)
        (body : list umicro)
| UScheduleCallback (delay : Z) (code : list umicro)
| UCheckPACT
(* Note there are no untyped equivalents to MUnkRead/MUnkWrite.  During
   `type_umicro`, if a UReadLink/UWriteLink points to an unknown field, it will
   be converted to an MUnkRead/MUnkWrite instead of MReadLink/MWriteLink. *)
| UHavocUpdate
| UHavocWrite (ol : field_link)
| UHavocProcess (fl : record_link)
.

(* Typed micro-operations.  Field-link operations are annotated with type
   information, wihch is used in the step relation to do value conversions. *)
Inductive micro : Set :=
(* Set a local field to a constant *)
| MSetConst (fn : field_name) (val : value)
(* Copy from one local field to another *)
| MCopy (fn_src : field_name) (src_ty : field_type)
        (fn_dest : field_name) (dest_ty : field_type)
(* Read a value through an input link and store it to a local field *)
| MReadLink (il : field_link) (il_ty : field_type) (fn : field_name) (f_ty : field_type)
(* Take the value of a local field and write it through an output link *)
| MWriteLink (fn : field_name) (f_ty : field_type) (ol : field_link) (ol_ty : field_type)
(* Invoke recursive processing of another record *)
| MProcess (fl : record_link)
(* Evaluate a CALC expression, and assign the result to the indicated local field *)
| MCalculate (expr : expr e_double 12) (fn_out : field_name)
(* Evaluate a CALC expression for a StrCalcOut record, and assign the result to
   the local field of the corresponding type *)
   (*
| MCalculateStr
        (expr : expr (e_double + e_string) 12)
        (fn_out_dbl : field_name) (fn_out_str : field_name)
        *)
(* Read a value from the hardware connected to the current record. *)
| MHwRead (fn : field_name) (f_ty : field_type)
(* Write a value to the hardware connected to the current record. *)
| MHwWrite (fn : field_name) (f_ty : field_type) (out_ty : field_type)
(* Conditionally execute some ops based on the current value, previous value,
 * and OOPT setting.  (For calcout records.)  All fields are TDouble. *)
| MCalcCond (fn_cur : field_name) (fn_prev : field_name) (oopt : output_exec)
        (body : list micro)
(* Schedule a callback to execute `code`, `delay` ticks in the future. *)
| MScheduleCallback (delay : Z) (code : list micro)
(* Check that PACT is zero, and cancel record processing if it isn't. *)
| MCheckPACT
(* Read from a field that has unknown semantics. *)
| MUnkRead (fn : field_name) (f_ty : field_type)
(* Write to a field that has unknown semantics. *)
| MUnkWrite
(* Havoc the current record's internal state.  Must be a `havoc_state` record *)
| MHavocUpdate
(* Write an arbitrary value to the output link. *)
| MHavocWrite (ol : field_link) (ol_ty : field_type)
(* Maybe process a record, or not (nondeterministically) *)
| MHavocProcess (fl : record_link)
. 

Inductive record_program : Set :=
    RecordProgram {
        rp_type : record_type;
        rp_code : list micro
    }.

Definition database_program := list record_program.

Notation lookup_program := (@lookup record_program).

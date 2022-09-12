Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import Omega.

Require Import Flocq.Appli.Fappli_IEEE.
Require Import v1.Util.
Require Import v1.Multi.
Require Import v1.NeutronTactics.
Require v1.FloatAux.

Require Import epics.SpecOpcodes.
Require Import epics.SpecRecords.
Require Import epics.SpecRecordData.
Require Import epics.SpecTypes.
Require Import expr.Expr.
Require expr.Dbl.


(* Input and output events *)

Inductive input_event : Set :=
| IProcess (rn : record_name)
| IRunCallback (rn : record_name) (ops : list micro)
.

Inductive output_event : Set :=
| OTraceInput (ie : input_event)
| OTraceBegin (rn : record_name) (rs : record_state)
| OTraceEnd (rn : record_name) (rs : record_state)
| OHwWrite (rn : record_name) (val : value)
| OScheduleCallback (delay : Z) (rn : record_name) (ops : list micro)
.


Inductive frame : Set :=
    Frame {
        frame_rn : record_name;
        frame_code : list micro
    }.

Inductive state : Set :=
    State {
        state_dbs : database_state;
        state_stk : list frame
    }.


(* Helper functions *)
Definition write_record_field dbs rn fn val :=
    update_record (fun rs => write_field rs fn val) dbs rn.

Definition read_record_field dbs rn fn :=
    lookup dbs rn >>= fun rs =>
    read_field rs fn.

Definition run_calculate_record (expr : multi 12 _ -> (multi 12 _ * _)) fn_out rs :=
    (* Not as generic as it could be, but much easier to work with... *)
    match rs with
    | RsCalc (CalcState a2l val) =>
            let (a2l', result) := expr a2l in
            match fn_out with
            | f_VAL => Some (RsCalc (CalcState a2l' result))
            | _ => None
            end

    | RsCalcOut (CalcOutState a2l val pval oval tmp0) =>
            let (a2l', result) := expr a2l in
            match fn_out with
            | f_VAL => Some (RsCalcOut (CalcOutState a2l' result pval oval tmp0))
            | f_OVAL => Some (RsCalcOut (CalcOutState a2l' val pval result tmp0))
            | _ => None
            end

    | _ => None
    end.

Definition run_calculate expr fn_out dbs rn :=
    update_record (run_calculate_record expr fn_out) dbs rn.

(*
Definition run_calculate_str_record (expr : multi 12 _ -> multi 12 _ -> _ + _)
        fn_out_dbl fn_out_str rs :=
    match rs with
    | RsStrCalcOut st =>
            let a2l := str_calc_out_A_to_L st in
            let aa2ll := str_calc_out_AA_to_LL st in
            match expr a2l aa2ll with
            | inl dbl => write_field rs fn_out_dbl (VDouble dbl)
            | inr str => write_field rs fn_out_str (VString str)
            end

    | _ => None
    end.

Definition run_calculate_str expr fn_out_dbl fn_out_str dbs rn :=
    update_record (run_calculate_str_record expr fn_out_dbl fn_out_str) dbs rn.
*)


Definition eval_calc_cond (cur : e_double) (prev : e_double) (oopt : output_exec) : bool :=
    let is_eq := e_double_is_eq in
    match oopt with
    | EveryTime => true
    | OnChange =>
            (* Special handling.  The EPICS code for this is:
             *     ! (fabs(prev - cur) <= 0.0)
             * which is identical to `prev == cur` except that it returns true,
             * not false, when `prev == cur == +/-inf`. *)
            match cur, prev with
            (* `cur == prev == +inf` and `cur == prev == -inf` cases *)
            | B754_infinity _ _ true, B754_infinity _ _ true => true
            | B754_infinity _ _ false, B754_infinity _ _ false => true
            | _, _ => negb (is_eq cur prev)
            end
    | WhenZero => is_eq cur d_zero
    | WhenNonzero => negb (is_eq cur d_zero)
    | TransitionToZero => andb (negb (is_eq prev d_zero)) (is_eq cur d_zero)
    | TransitionToNonzero => andb (is_eq prev d_zero) (negb (is_eq cur d_zero))
    end.




Inductive is_numeric : field_type -> Prop :=
| NumDouble : is_numeric TDouble
| NumEnum : is_numeric TEnum
| NumLong : is_numeric TLong
.

Definition convert_value (v : value) (ty : field_type) (v' : value) : Prop.
refine (
    value_type v' = ty /\
    match v, ty with
    | VDouble _, TDouble => v' = v
    | VDouble d, TEnum =>
            match FloatAux.B2Z_safe d with
            | Some z => forall pf : (0 <= z < ENUM_MAX)%Z, v' = VEnum (EEnum z _)
            | None => True
            end
    | VDouble d, TLong =>
            match FloatAux.B2Z_safe d with
            | Some z => forall pf : (-LONG_MAX <= z < LONG_MAX)%Z,
                    v' = VLong (ELong z _)
            | None => True
            end
    | VDouble _, _ => True

    | VEnum (EEnum z Hlt), TDouble =>
            (* No precondition.  The 16-bit `enum` range falls within the
               52-bit precise double range. *)
            v' = VDouble (FloatAux.Z2B64 z)
    | VEnum _, TEnum => v' = v
    | VEnum (EEnum z Hlt), TLong =>
            (* The unsigned 16-bit enum range lies entirely within the 32-bit
               signed long range. *)
            v' = VLong (ELong z _)
    | VEnum _, _ => True

    | VLong (ELong z Hlt), TDouble =>
            (* No precondition.  The 32-bit `long` range falls within the
               52-bit precise double range. *)
            v' = VDouble (FloatAux.Z2B64 z)
    | VLong (ELong z Hlt), TEnum =>
            forall pf : (0 <= z < ENUM_MAX)%Z, v' = VEnum (EEnum z _)
    | VLong (ELong z Hlt), TLong => v' = v
    | VLong _, _ => True

    | VString s, TString => v' = v
    | VString _, _ => True

    | @VArray ty n a, TArray ty' n' => ty' = ty -> n' = n -> v' = v
    | VArray _, _ => True
    end
); hide.
- auto.
- auto.
- assert (ENUM_MAX < LONG_MAX)%Z. { compute. auto. }
  omega.
- auto.
Defined.


(* Basic steps that modify only the database. *)
Inductive db_step :
    record_name -> micro -> database_state -> database_state -> Prop :=
| SSetConst : forall rn fn val dbs,
        forall dbs', write_record_field dbs rn fn val = Some dbs' ->
        db_step rn (MSetConst fn val) dbs dbs'
| SCopy : forall rn fn_src src_ty fn_dest dest_ty dbs,
        forall val, read_record_field dbs rn fn_src = Some val ->
        value_type val = src_ty ->
        forall val', convert_value val dest_ty val' ->
        forall dbs', write_record_field dbs rn fn_dest val' = Some dbs' ->
        db_step rn (MCopy fn_src src_ty fn_dest dest_ty) dbs dbs'
| SReadLink : forall rn il il_ty fn f_ty dbs,
        forall val, read_record_field dbs (fl_rn il) (fl_fn il) = Some val ->
        value_type val = il_ty ->
        forall val', convert_value val f_ty val' ->
        forall dbs', write_record_field dbs rn fn val' = Some dbs' ->
        db_step rn (MReadLink il il_ty fn f_ty) dbs dbs'
| SWriteLink : forall rn fn f_ty ol ol_ty dbs,
        forall val, read_record_field dbs rn fn = Some val ->
        value_type val = f_ty ->
        forall val', convert_value val ol_ty val' ->
        forall dbs', write_record_field dbs (fl_rn ol) (fl_fn ol) val' = Some dbs' ->
        db_step rn (MWriteLink fn f_ty ol ol_ty) dbs dbs'
| SCalculate : forall rn expr fn_out dbs,
        forall f, expr.Dbl.denote expr = Some f ->
        forall dbs', run_calculate f fn_out dbs rn = Some dbs' ->
        db_step rn (MCalculate expr fn_out) dbs dbs'
        (*
| SCalculateStr : forall rn expr fn_out_dbl fn_out_str dbs,
        forall f, expr.DblStr.denote expr = Some f ->
        (* TODO: no_side_effects expr *)
        let f' := (fun sd ss => let '(_sd', _ss', x) := f sd ss in x) in
        forall dbs', run_calculate_str f' fn_out_dbl fn_out_str dbs rn = Some dbs' ->
        db_step rn (MCalculateStr expr fn_out_dbl fn_out_str) dbs dbs'
        *)
| SHwRead : forall rn fn f_ty dbs,
        (* TODO should probably interact with the i/o trace *)
        forall val, value_type val = f_ty ->
        forall dbs', write_record_field dbs rn fn val = Some dbs' ->
        db_step rn (MHwRead fn f_ty) dbs dbs'
| SUnkRead : forall rn fn f_ty dbs,
        forall val, value_type val = f_ty ->
        forall dbs', write_record_field dbs rn fn val = Some dbs' ->
        db_step rn (MUnkRead fn f_ty) dbs dbs'
| SUnkWrite : forall rn dbs,
        db_step rn (MUnkWrite) dbs dbs
| SHavocUpdate : forall rn dbs rs',
        forall rs, lookup_state dbs rn = Some rs ->
        record_state_type rs' = record_state_type rs ->
        forall dbs', update_record (fun _ => Some rs') dbs rn = Some dbs' ->
        db_step rn (MHavocUpdate) dbs dbs'
| SHavocWrite : forall rn ol ol_ty dbs val,
        value_type val = ol_ty ->
        forall dbs', write_record_field dbs (fl_rn ol) (fl_fn ol) val = Some dbs' ->
        db_step rn (MHavocWrite ol ol_ty) dbs dbs'
.

Inductive output_step :
    record_name -> micro -> database_state -> output_event -> Prop :=
| SHwWrite : forall rn fn f_ty out_ty dbs,
        forall val, read_record_field dbs rn fn = Some val ->
        value_type val = f_ty ->
        forall val', convert_value val out_ty val' ->
        output_step rn (MHwWrite fn f_ty out_ty) dbs (OHwWrite rn val')
| SScheduleCallback : forall rn delay code dbs,
        output_step rn (MScheduleCallback delay code) dbs (OScheduleCallback delay rn code)
.


Inductive step (dbp : database_program) :
    state -> state -> list output_event -> Prop :=
| SDb : forall dbs rn m rest stk,
        forall dbs', db_step rn m dbs dbs' ->
        step dbp
            (State dbs (Frame rn (m :: rest) :: stk))
            (State dbs' (Frame rn rest :: stk))
            []
| SOutput : forall dbs rn m rest stk,
        forall out, output_step rn m dbs out ->
        step dbp
            (State dbs (Frame rn (m :: rest) :: stk))
            (State dbs (Frame rn rest :: stk))
            [out]
| SPop : forall dbs rn stk,
        forall rs, lookup dbs rn = Some rs ->
        step dbp
            (State dbs (Frame rn [] :: stk))
            (State dbs (stk))
            [OTraceEnd rn rs]
| SProcess : forall dbs rn fl rest stk,
        let rn' := rl_rn fl in
        forall rp, lookup_program dbp rn' = Some rp ->
        forall rs, lookup dbs rn' = Some rs ->
        step dbp
            (State dbs (Frame rn (MProcess fl :: rest) :: stk))
            (State dbs (Frame rn' (rp_code rp) :: Frame rn rest :: stk))
            [OTraceBegin rn' rs]

| SCalcCondNo : forall dbs rn fn_cur fn_prev oopt body rest stk,
        forall cur_val, read_record_field dbs rn fn_cur = Some cur_val ->
        forall cur, cur_val = VDouble cur ->
        forall prev_val, read_record_field dbs rn fn_prev = Some prev_val ->
        forall prev, prev_val = VDouble prev ->
        eval_calc_cond cur prev oopt = false ->
        step dbp
            (State dbs (Frame rn (MCalcCond fn_cur fn_prev oopt body :: rest) :: stk))
            (State dbs (Frame rn rest :: stk))
            []
| SCalcCondYes : forall dbs rn fn_cur fn_prev oopt body rest stk,
        forall cur_val, read_record_field dbs rn fn_cur = Some cur_val ->
        forall cur, cur_val = VDouble cur ->
        forall prev_val, read_record_field dbs rn fn_prev = Some prev_val ->
        forall prev, prev_val = VDouble prev ->
        eval_calc_cond cur prev oopt = true ->
        step dbp
            (State dbs (Frame rn (MCalcCond fn_cur fn_prev oopt body :: rest) :: stk))
            (State dbs (Frame rn (body ++ rest) :: stk))
            []

| SCheckPACTZero : forall dbs rn rest stk,
        forall val, read_record_field dbs rn f_PACT = Some val ->
        forall pact, unwrap_enum val = Some pact ->
        enum_val pact = 0%Z ->
        step dbp
            (State dbs (Frame rn (MCheckPACT :: rest) :: stk))
            (State dbs (Frame rn rest :: stk))
            []
| SCheckPACTNonZero : forall dbs rn rest stk,
        forall val, read_record_field dbs rn f_PACT = Some val ->
        forall pact, unwrap_enum val = Some pact ->
        enum_val pact <> 0%Z ->
        step dbp
            (State dbs (Frame rn (MCheckPACT :: rest) :: stk))
            (* Leave an empty frame for SPop to handle *)
            (State dbs (Frame rn [] :: stk))
            []

| SHavocProcessNo : forall dbs rn fl rest stk,
        step dbp
            (State dbs (Frame rn (MHavocProcess fl :: rest) :: stk))
            (State dbs (Frame rn rest :: stk))
            []
| SHavocProcessYes : forall dbs rn fl rest stk,
        let rn' := rl_rn fl in
        forall rp, lookup_program dbp rn' = Some rp ->
        forall rs, lookup dbs rn' = Some rs ->
        step dbp
            (State dbs (Frame rn (MHavocProcess fl :: rest) :: stk))
            (State dbs (Frame rn' (rp_code rp) :: Frame rn rest :: stk))
            [OTraceBegin rn' rs]
.

Inductive star_step (dbp : database_program) :
    state -> state -> list output_event -> Prop :=
| SsNil : forall state,
        star_step dbp state state []
| SsCons : forall state,
        forall state' oes1, step dbp state state' oes1 ->
        forall state'' oes2, star_step dbp state' state'' oes2 ->
        star_step dbp state state'' (oes1 ++ oes2)
.


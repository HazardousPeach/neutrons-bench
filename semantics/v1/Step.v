Require Import Arith.
Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import Omega.

Require Import v1.Multi.
Require Import v1.Util.
Require Import v1.Expr.
Require Import v1.NeutronTactics.
Require Import v1.FloatAux.
Require v1.ExprDbl.
Require v1.ExprDblStr.

Require Export v1.EpicsTypes.
Require Export v1.EpicsRecords.

Set Default Timeout 10.
Set Implicit Arguments.



(* Spec: umicro + compilation *)

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
| UCalculateStr
        (expr : expr (e_double + e_string) 12)
        (fn_out_dbl : field_name)
        (fn_out_str : field_name)
| UHwWrite (fn : field_name) (out_ty : field_type)
| UCalcCond (fn_cur : field_name) (fn_prev : field_name) (oopt : output_exec)
        (body : list umicro)
| UScheduleCallback (delay : Z) (code : list umicro)
| UCheckPACT
| UHavocUpdate
| UHavocWrite (ol : field_link)
| UHavocProcess (fl : record_link)
.

Inductive record_uprogram : Set :=
    RecordUProgram {
        ru_type : record_type;
        ru_code : list umicro
    }.

Definition database_uprogram := list record_uprogram.


Definition compile_process_passive pp rn :=
    match pp with
    | PP => [UProcess (RecordLink rn)]
    | NPP => []
    end.

Definition compile_in_link il fn :=
    match il with
    | InLinkNull => []
    | InLinkConstant x => [USetConst fn (VDouble x)]
    | InLinkField fl =>
            compile_process_passive (fl_pp fl) (fl_rn fl) ++
            [UReadLink fl fn]
    end.

Definition compile_out_link fn ol :=
    match ol with
    | OutLinkNull => []
    | OutLinkField fl =>
            [UWriteLink fn fl] ++
            compile_process_passive (fl_pp fl) (fl_rn fl)
    end.

Definition compile_out_link_typed ty_fns ol :=
    match ol with
    | OutLinkNull => []
    | OutLinkField fl =>
            match fl_fn fl with
            (* Special handling for PROC.  Writing to PROC (regardless of
               value) causes the target record to process. *)
            | f_PROC => [UProcess (RecordLink (fl_rn fl))]
            | _ =>
                    [UWriteLinkTyped ty_fns fl] ++
                    compile_process_passive (fl_pp fl) (fl_rn fl)
            end
    end.

Definition compile_out_link_havoc ol :=
    match ol with
    | OutLinkNull => []
    | OutLinkField fl =>
            match fl_fn fl with
            | f_PROC => [UHavocProcess (RecordLink (fl_rn fl))]
            | _ =>
                    [UHavocWrite fl] ++
                    compile_process_passive (fl_pp fl) (fl_rn fl)
            end
    end.

Definition compile_fwd_link fl :=
    match fl with
    | FwdLinkNull => []
    | FwdLinkRecord rl => [UProcess rl]
    end.


Definition compile_calc_cond fn_cur fn_prev oopt body :=
    [UCalcCond fn_cur fn_prev oopt body].

Definition for_each (n : nat) (f : index n -> list umicro) : list umicro :=
    concat (map f (index_list n)).

Definition compile_record (rc : record_config) : record_uprogram :=
    let ops :=
        match rc with

        | RcCalc (CalcConfig CALC INPA_to_INPL FLNK) =>
                for_each (fun i =>
                    compile_in_link (INPA_to_INPL !! i) (f_A_to_L i)) ++
                [ UCalculate CALC f_VAL ] ++
                compile_fwd_link FLNK

        | RcCalcOut (CalcOutConfig CALC OCAL INPA_to_INPL OUT FLNK OOPT DOPT) =>
                for_each (fun i =>
                    compile_in_link (INPA_to_INPL !! i) (f_A_to_L i)) ++
                [ UCalculate CALC f_VAL ] ++
                (* The actual C code works like this:
                    - run CALC
                    - check OOPT, VAL, PVAL to decide whether or not to write OUT
                    - set PVAL = VAL
                    - (maybe) write OUT
                   Here, the checking of OOPT/VAL/PVAL and writing of OUT are
                   tied together, so we need an extra temporary. *)
                [ UCopy f_PVAL (f_tmp 0);
                  UCopy f_VAL f_PVAL ] ++
                compile_calc_cond f_VAL (f_tmp 0) OOPT (
                    (* DOPT determines how to populate OVAL: run OCAL, or copy
                       from VAL? *)
                    match DOPT with
                    | UseCalc => [ UCopy f_VAL f_OVAL ]
                    | UseOcal => [ UCalculate OCAL f_OVAL ]
                    end ++
                    compile_out_link f_OVAL OUT
                ) ++
                compile_fwd_link FLNK

        | RcStrCalcOut (StrCalcOutConfig CALC OCAL INPA_to_INPL INAA_to_INLL OUT FLNK OOPT DOPT) =>
                for_each (fun i =>
                    compile_in_link (INPA_to_INPL !! i) (f_A_to_L i)) ++
                for_each (fun i =>
                    compile_in_link (INAA_to_INLL !! i) (f_AA_to_LL i)) ++
                [ UCalculateStr CALC f_VAL f_SVAL ] ++
                [ UCopy f_PVAL (f_tmp 0);
                  UCopy f_VAL f_PVAL ] ++
                compile_calc_cond f_VAL (f_tmp 0) OOPT (
                    match DOPT with
                    | UseCalc => [ UCopy f_VAL f_OVAL; UCopy f_SVAL f_OSV ]
                    | UseOcal => [ UCalculateStr OCAL f_OVAL f_OSV ]
                    end ++
                    compile_out_link_typed
                        [(MatchAnyNumeric, f_OVAL); (MatchExact TString, f_OSV)] OUT
                ) ++
                compile_fwd_link FLNK

        | RcArrayCalcOut n (ArrayCalcOutConfig _ CALC OCAL INPA_to_INPL INAA_to_INLL OUT FLNK OOPT DOPT) =>
                for_each (fun i =>
                    compile_in_link (INPA_to_INPL !! i) (f_A_to_L i)) ++
                for_each (fun i =>
                    compile_in_link (INAA_to_INLL !! i) (f_AA_to_LL i)) ++
                [ UHavocUpdate ] ++
                compile_out_link_havoc OUT ++
                compile_fwd_link FLNK

        | RcFanout (FanoutConfig LNK1_to_LNK6) =>
                for_each (fun i =>
                    compile_fwd_link (LNK1_to_LNK6 !! i))

        | RcDFanout (DFanoutConfig DOL OUTA_to_OUTH FLNK) =>
                compile_in_link DOL f_VAL ++
                for_each (fun i =>
                    compile_out_link f_VAL (OUTA_to_OUTH !! i)) ++
                compile_fwd_link FLNK

        | RcSeq (SeqConfig DOL1_to_DOLA LNK1_to_LNKA) =>
                [ UCheckPACT;
                  USetConst f_PACT (VEnum (EEnum 2 1 ltac:(hide; omega))) ] ++
                (* The callbacks are not all scheduled at once.  Instead, each
                   callback schedules the next in the sequence.  The difference
                   becomes observable when the first callback of one `seq`
                   record triggers processing of another `seq` record - the two
                   sets of link updates should be interleaved. *)
                fold_right (fun i next =>
                        let in_link := DOL1_to_DOLA !! i in
                        let out_link := LNK1_to_LNKA !! i in
                        (* Don't schedule callbacks for unused DOLx/OUTx slots,
                         * just run the next step immediately. *)
                        match in_link, out_link with
                        | InLinkNull, OutLinkNull => next
                        | _, _ =>
                            [UScheduleCallback 0
                                (compile_in_link in_link (f_DO1_to_DOA i) ++
                                 compile_out_link (f_DO1_to_DOA i) out_link ++
                                 next)
                            ]
                        end)
                    (* Last thing to do: reset PACT.  This happens at the end
                     * of the last callback. *)
                    [ USetConst f_PACT (VEnum (EEnum 2 0 ltac:(hide; omega))) ]
                    (index_list _)

        | RcWaveform ty n (WaveformConfig _ _ INP FLNK) =>
                compile_in_link INP f_VAL ++
                [ UHavocUpdate ] ++
                compile_fwd_link FLNK

        | RcAnalogIn (AnalogInConfig FLNK) =>
                compile_fwd_link FLNK

        | RcAnalogOut (AnalogOutConfig DOL FLNK) =>
                (* ao records prevent db/CA writes to the VAL field by storing
                   a second copy of VAL in PVAL and restoring on every process.
                   Note this isn't completely foolproof - it's possible for a
                   PP INLINK to trigger a write followed by a read, and the
                   read will see the written value. *)
                [ UCopy f_PVAL f_VAL ] ++
                compile_in_link DOL f_VAL ++
                [ UCopy f_VAL f_PVAL ] ++
                [UHwWrite f_VAL TDouble] ++
                compile_fwd_link FLNK

        | RcBinaryIn (BinaryInConfig FLNK) =>
                compile_fwd_link FLNK

        | RcBinaryOut (BinaryOutConfig DOL FLNK) =>
                compile_in_link DOL f_VAL ++
                [UHwWrite f_VAL (TEnum 2)] ++
                compile_fwd_link FLNK

        | RcMBBO (MBBOConfig DOL FLNK) =>
                compile_in_link DOL f_VAL ++
                [UHwWrite f_VAL (TEnum 16)] ++
                compile_fwd_link FLNK

        | RcStringIn (StringInConfig FLNK) =>
                compile_fwd_link FLNK

        | RcStringOut (StringOutConfig DOL FLNK) =>
                compile_in_link DOL f_VAL ++
                [UHwWrite f_VAL TString] ++
                compile_fwd_link FLNK

        | RcLongIn (LongInConfig FLNK) =>
                compile_fwd_link FLNK

        | RcLongOut (LongOutConfig DOL FLNK) =>
                compile_in_link DOL f_VAL ++
                [UHwWrite f_VAL TLong] ++
                compile_fwd_link FLNK

        | RcAsyn (AsynConfig) => []

        | RcSubarray ty n m (SubarrayConfig _ _ _ INP INDX FLNK) =>
                compile_in_link INP (f_tmp 0) ++
                [ UHavocUpdate ] ++
                compile_fwd_link FLNK

        end in
    RecordUProgram (record_config_type rc) ops.

Definition compile_database (dbc : database_config) : database_uprogram :=
    map compile_record dbc.


(* Spec: micro + link typing *)

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
| MCalculateStr
        (expr : expr (e_double + e_string) 12)
        (fn_out_dbl : field_name) (fn_out_str : field_name)
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

Definition record_program_type := rp_type.
Definition database_program_type dbp :=
    map record_program_type dbp.


Definition type_umicro dbt rt : umicro -> option micro :=
    let fix go uop : option micro :=
        let fix go_list uops : option (list micro) :=
            match uops with
            | [] => Some []
            | uop :: uops =>
                    go uop >>= fun uop' =>
                    go_list uops >>= fun uops' =>
                    Some (uop' :: uops')
            end in
        match uop with
        | USetConst fn val => Some (MSetConst fn val)
        | UCopy fn_src fn_dest =>
                (* The imprecision of `record_field_type` is okay here because the
                 * result is wrong only when the field name is invalid. *)
                let src_ty := record_field_type rt fn_src in
                let dest_ty := record_field_type rt fn_dest in
                Some (MCopy fn_src src_ty fn_dest dest_ty)
        | UReadLink il fn =>
                (* The imprecision of `record_field_type` is okay here because the
                 * result is wrong only when the field name is invalid. *)
                let f_ty := record_field_type rt fn in
                lookup_type dbt (fl_rn il) >>= fun il_rt =>
                let il_ty := record_field_type il_rt (fl_fn il) in
                Some (MReadLink il il_ty fn f_ty)
        | UWriteLink fn ol =>
                let f_ty := record_field_type rt fn in
                lookup_type dbt (fl_rn ol) >>= fun ol_rt =>
                let ol_ty := record_field_type ol_rt (fl_fn ol) in
                Some (MWriteLink fn f_ty ol ol_ty)
        | UWriteLinkTyped fns ol =>
                (* This one has special handling.  UWriteLinkTyped chooses one of
                   several local fields to write, depending on the type of the
                   target of the out_link.  In this case, now that the output link
                   type is known, we can look up the actual local field to use and
                   generate an ordinary MWriteLink instead. *)
                lookup_type dbt (fl_rn ol) >>= fun ol_rt =>
                let ty := record_field_type ol_rt (fl_fn ol) in
                find_match_for_type fns ty >>= fun fn =>
                Some (MWriteLink fn ty ol ty)
        | UProcess fl => Some (MProcess fl)
        | UCalculate expr fn_out => Some (MCalculate expr fn_out)
        | UCalculateStr expr fn_out_dbl fn_out_str =>
                Some (MCalculateStr expr fn_out_dbl fn_out_str)
        | UHwWrite fn out_ty =>
                let f_ty := record_field_type rt fn in
                Some (MHwWrite fn f_ty out_ty)
        | UCalcCond fn_cur fn_prev oopt body =>
                go_list body >>= fun body' =>
                Some (MCalcCond fn_cur fn_prev oopt body')
        | UScheduleCallback delay code =>
                go_list code >>= fun code' =>
                Some (MScheduleCallback delay code')
        | UCheckPACT => Some (MCheckPACT)
        | UHavocUpdate => Some (MHavocUpdate)
        | UHavocWrite ol =>
                lookup_type dbt (fl_rn ol) >>= fun ol_rt =>
                let ol_ty := record_field_type ol_rt (fl_fn ol) in
                Some (MHavocWrite ol ol_ty)
        | UHavocProcess fl => Some (MHavocProcess fl)
        end in go.

Definition type_record_uprogram dbt urp : option record_program :=
    map_opt (type_umicro dbt (ru_type urp)) (ru_code urp) >>= fun code =>
    Some (RecordProgram (ru_type urp) code).

Definition type_database_program' dbt udp : option database_program :=
    map_opt (type_record_uprogram dbt) udp.

Definition type_database_program udp : option database_program :=
    type_database_program' (map ru_type udp) udp.


(* Spec: implicit conversions *)

Definition range_check low high x : ({ low <= x < high } + { x < low \/ x >= high })%Z.
destruct (Z_lt_dec x low).
  { right. eauto. }
destruct (Z_ge_dec x high).
  { right. eauto. }
left. omega.
Defined.

Definition convert_value (val : value) (ty : field_type) : option value.
refine (
    match val with
    | VDouble x =>
            match ty with
            | TDouble => Some (VDouble x)
            | TEnum max =>
                    if Z_le_dec max 0 then None else
                    let val := B2Z_trunc x in
                    if range_check 0 max val
                        then Some (VEnum (EEnum max val _))
                        else None
            | TLong =>
                    let val := B2Z_trunc x in
                    if range_check (-LONG_MAX)%Z LONG_MAX val
                        then Some (VLong (ELong val _))
                        else None
            | _ => None
            end
    | VString x =>
            match ty with
            | TString => Some (VString x)
            | _ => None
            end
    | @VEnum max (EEnum _ x Hlt)  =>
            match ty with
            | TDouble => Some (VDouble (Z2B64 x))
            | TEnum max' =>
                    if Z_le_dec max max'
                        then Some (@VEnum max' (EEnum _ x _))
                        else None
            | TLong =>
                    if range_check (-LONG_MAX)%Z LONG_MAX x
                        then Some (VLong (ELong x _))
                        else None
            | _ => None
            end
    | VLong (ELong x Hlt) =>
            match ty with
            | TDouble => Some (VDouble (Z2B64 x))
            | TEnum max =>
                    if Z_le_dec max 0 then None else
                    if range_check 0 max x
                        then Some (VEnum (EEnum max x _))
                        else None
            | TLong => Some (VLong (ELong x Hlt))
            | _ => None
            end
    | @VArray elem size arr  =>
            match ty with
            | TArray elem' size' =>
                    if elem_type_eq_dec elem elem' then
                        if eq_nat_dec size size' then
                            Some (VArray arr)
                        else None
                    else None
            | _ => None
            end
    end
); hide.
all: try omega.
Defined.


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


(* Spec: step relation *)

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


Definition eval_calc_cond (cur : e_double) (prev : e_double) (oopt : output_exec) : bool :=
    let is_eq x y := if e_double_eq_dec x y then true else false in
    match oopt with
    | EveryTime => true
    | OnChange => negb (is_eq cur prev)
    | WhenZero => is_eq cur zero
    | WhenNonzero => negb (is_eq cur zero)
    | TransitionToZero => andb (negb (is_eq prev zero)) (is_eq cur zero)
    | TransitionToNonzero => andb (is_eq prev zero) (negb (is_eq cur zero))
    end.

(* Basic steps that modify only the database. *)
Inductive db_step :
    record_name -> micro -> database_state -> database_state -> Prop :=
| SSetConst : forall rn fn val dbs,
        forall dbs', write_record_field dbs rn fn val = Some dbs' ->
        db_step rn (MSetConst fn val) dbs dbs'
| SCopy : forall rn fn_src src_ty fn_dest dest_ty dbs,
        forall val, read_record_field dbs rn fn_src = Some val ->
        value_type val = src_ty ->
        forall val', convert_value val dest_ty = Some val' ->
        forall dbs', write_record_field dbs rn fn_dest val' = Some dbs' ->
        db_step rn (MCopy fn_src src_ty fn_dest dest_ty) dbs dbs'
| SReadLink : forall rn il il_ty fn f_ty dbs,
        forall val, read_record_field dbs (fl_rn il) (fl_fn il) = Some val ->
        value_type val = il_ty ->
        forall val', convert_value val f_ty = Some val' ->
        forall dbs', write_record_field dbs rn fn val' = Some dbs' ->
        db_step rn (MReadLink il il_ty fn f_ty) dbs dbs'
| SWriteLink : forall rn fn f_ty ol ol_ty dbs,
        forall val, read_record_field dbs rn fn = Some val ->
        value_type val = f_ty ->
        forall val', convert_value val ol_ty = Some val' ->
        forall dbs', write_record_field dbs (fl_rn ol) (fl_fn ol) val' = Some dbs' ->
        db_step rn (MWriteLink fn f_ty ol ol_ty) dbs dbs'
| SCalculate : forall rn expr fn_out dbs,
        forall f, ExprDbl.denote expr = Some f ->
        forall dbs', run_calculate f fn_out dbs rn = Some dbs' ->
        db_step rn (MCalculate expr fn_out) dbs dbs'
| SCalculateStr : forall rn expr fn_out_dbl fn_out_str dbs,
        forall f, ExprDblStr.denote expr = Some f ->
        (* TODO: no_side_effects expr *)
        let f' := (fun sd ss => let '(_sd', _ss', x) := f sd ss in x) in
        forall dbs', run_calculate_str f' fn_out_dbl fn_out_str dbs rn = Some dbs' ->
        db_step rn (MCalculateStr expr fn_out_dbl fn_out_str) dbs dbs'
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
        forall val', convert_value val out_ty = Some val' ->
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
        forall rp, lookup_program dbp (rl_rn fl) = Some rp ->
        forall rs, lookup dbs rn = Some rs ->
        step dbp
            (State dbs (Frame rn (MProcess fl :: rest) :: stk))
            (State dbs (Frame (rl_rn fl) (rp_code rp) :: Frame rn rest :: stk))
            [OTraceBegin (rl_rn fl) rs]

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
        val = VEnum (EEnum 2 0 ltac:(hide; omega)) ->
        step dbp
            (State dbs (Frame rn (MCheckPACT :: rest) :: stk))
            (State dbs (Frame rn rest :: stk))
            []
| SCheckPACTNonZero : forall dbs rn rest stk,
        forall val, read_record_field dbs rn f_PACT = Some val ->
        val <> VEnum (EEnum 2 0 ltac:(hide; omega)) ->
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
        forall rp, lookup_program dbp (rl_rn fl) = Some rp ->
        step dbp
            (State dbs (Frame rn (MHavocProcess fl :: rest) :: stk))
            (State dbs (Frame (rl_rn fl) (rp_code rp) :: Frame rn rest :: stk))
            []
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

Inductive start_handle (dbp : database_program) :
    input_event -> frame -> Prop :=
| ShProcess : forall rn,
        forall rp, lookup dbp rn = Some rp ->
        start_handle dbp (IProcess rn) (Frame rn (rp_code rp))
| ShRunCallback : forall rn code,
        start_handle dbp (IRunCallback rn code) (Frame rn code)
.

Inductive handle (dbp : database_program) :
    database_state -> input_event -> database_state -> list output_event -> Prop :=
| Handle : forall dbs ie,
        forall fr, start_handle dbp ie fr ->
        forall rs, lookup dbs (frame_rn fr) = Some rs ->
        forall dbs' oes, star_step dbp (State dbs [fr]) (State dbs' []) oes ->
        let trace_input := OTraceInput ie in
        let trace_begin := OTraceBegin (frame_rn fr) rs in
        handle dbp dbs ie dbs' (trace_input :: trace_begin :: oes).

Inductive handle_many (dbp : database_program) :
    database_state -> list input_event -> database_state -> list output_event -> Prop :=
| HmNil : forall dbs, handle_many dbp dbs [] dbs []
| HmCons : forall dbs ie ies,
        forall dbs' oes1, handle dbp dbs ie dbs' oes1 ->
        forall dbs'' oes2, handle_many dbp dbs' ies dbs'' oes2 ->
        handle_many dbp dbs (ie :: ies) dbs'' oes2.

Require Import List.
Import ListNotations.
Require Import Omega.

Require Import v1.Multi.
Require Import v1.NeutronTactics.
Require Import v1.Util.

Require Import epics.SpecOpcodes.
Require Import epics.SpecRecords.
Require Import epics.SpecRecordData.
Require Import epics.SpecTypes.


(* Compile a database configuration to a micro-op program. *)

(* Generic helpers *)
Definition for_each {n : nat} (f : index n -> list umicro) : list umicro :=
    concat (map f (index_list n)).

(* Helpers for compiling various common constructs. *)
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
            match fl_fn fl with
            | f_PROC =>
                    [UProcess (RecordLink (fl_rn fl))] ++
                    compile_process_passive (fl_pp fl) (fl_rn fl)

            | _ =>
                    [UWriteLink fn fl] ++
                    compile_process_passive (fl_pp fl) (fl_rn fl)
            end
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

Definition compile_record_untyped (rc : record_config) : list umicro :=
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
            [ UCopy f_PVAL (f_tmp0);
              UCopy f_VAL f_PVAL ] ++
            compile_calc_cond f_VAL (f_tmp0) OOPT (
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
            [ UHavocUpdate ] ++
            [ UCopy f_PVAL (f_tmp0);
              UCopy f_VAL f_PVAL ] ++
            compile_calc_cond f_VAL (f_tmp0) OOPT (
                match DOPT with
                | UseCalc => [ UCopy f_VAL f_OVAL; UCopy f_SVAL f_OSV ]
                (* For UseOcal, we havoc the record state again to reflect the
                 * effect of the OCAL evaluation.  This is somewhat redundant,
                 * since most fields are already havoc, but it makes
                 * UHavocUpdates match up with SCALC_PERFORM trace events. *)
                | UseOcal => [ UHavocUpdate ]
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
              USetConst f_PACT (VEnum (EEnum 1 ltac:(hide; compute; split; congruence))) ] ++
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
                [ USetConst f_PACT (VEnum (EEnum 0 ltac:(hide; compute; split; congruence))) ]
                (index_list _)

    | RcWaveform ty n (WaveformConfig _ _ INP FLNK) =>
            compile_in_link INP f_VAL ++
            [ UHavocUpdate ] ++
            compile_fwd_link FLNK

    | RcAnalogIn (AnalogInConfig FLNK) =>
            (*[UHwRead f_VAL] ++*)
            compile_fwd_link FLNK

    | RcAnalogOut (AnalogOutConfig DOL FLNK) =>
            (* ao records prevent db/CA writes to the VAL field by storing
               a second copy of VAL in PVAL and restoring on every process.
               Note this isn't completely foolproof - it's possible for a
               PP INLINK to trigger a write followed by a read, and the
               read will see the written value. *)
            let should_copy := match DOL with
            | InLinkField _ => true
            | _ => false
            end in
            (if should_copy then [ UCopy f_PVAL f_VAL ] else []) ++
            compile_in_link DOL f_VAL ++
            [ UCopy f_VAL f_PVAL ] ++
            [ UHwWrite f_VAL TDouble ] ++
            compile_fwd_link FLNK

    | RcBinaryIn (BinaryInConfig FLNK) =>
            (*[UHwRead f_VAL] ++*)
            compile_fwd_link FLNK

    | RcBinaryOut (BinaryOutConfig DOL FLNK) =>
            compile_in_link DOL f_VAL ++
            [UHwWrite f_VAL TEnum] ++
            compile_fwd_link FLNK

    | RcMBBO (MBBOConfig DOL FLNK) =>
            compile_in_link DOL f_VAL ++
            [UHwWrite f_VAL TEnum] ++
            compile_fwd_link FLNK

    | RcStringIn (StringInConfig FLNK) =>
            (*[UHwRead f_VAL] ++*)
            compile_fwd_link FLNK

    | RcStringOut (StringOutConfig DOL FLNK) =>
            compile_in_link DOL f_VAL ++
            [UHwWrite f_VAL TString] ++
            compile_fwd_link FLNK

    | RcLongIn (LongInConfig FLNK) =>
            (*[UHwRead f_VAL] ++*)
            compile_fwd_link FLNK

    | RcLongOut (LongOutConfig DOL FLNK) =>
            compile_in_link DOL f_VAL ++
            [UHwWrite f_VAL TLong] ++
            compile_fwd_link FLNK

    | RcAsyn (AsynConfig) => []

    | RcSubarray ty n m (SubarrayConfig _ _ _ INP INDX FLNK) =>
            compile_in_link INP (f_tmp0) ++
            [ UHavocUpdate ] ++
            compile_fwd_link FLNK

    end.


(* Add type annotations to a micro-op.  This can fail if link targets don't
   exist, or if certain links are ill-typed. *)
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
                do src_ty <- record_field_type rt fn_src ;;
                do dest_ty <- record_field_type rt fn_dest ;;
                Some (MCopy fn_src src_ty fn_dest dest_ty)
        | UReadLink il fn =>
                do f_ty <- record_field_type rt fn ;;
                do il_rt <- lookup_type dbt (fl_rn il) ;;
                match record_field_type il_rt (fl_fn il) with
                | Some il_ty => Some (MReadLink  il il_ty fn f_ty)
                | None => Some (MUnkRead fn f_ty)
                end
        | UWriteLink fn ol =>
                do f_ty <- record_field_type rt fn ;;
                do ol_rt <- lookup_type dbt (fl_rn ol) ;;
                match record_field_type ol_rt (fl_fn ol) with
                | Some ol_ty => Some (MWriteLink fn f_ty ol ol_ty)
                | None => Some (MUnkWrite)
                end
        | UWriteLinkTyped fns ol =>
                (* This one has special handling.  UWriteLinkTyped chooses one of
                   several local fields to write, depending on the type of the
                   target of the out_link.  In this case, now that the output link
                   type is known, we can look up the actual local field to use and
                   generate an ordinary MWriteLink instead. *)
                do ol_rt <- lookup_type dbt (fl_rn ol) ;;
                match record_field_type ol_rt (fl_fn ol) with
                | Some ol_ty =>
                        do fn <- find_match_for_type fns ol_ty ;;
                        (* Note the match may be fuzzy, so we still need to
                           look up the local field type .*)
                        do f_ty <- record_field_type rt fn ;;
                        Some (MWriteLink fn f_ty ol ol_ty)
                | None => Some (MUnkWrite)
                end
        | UProcess fl => Some (MProcess fl)
        | UCalculate expr fn_out => Some (MCalculate expr fn_out)
                (*
        | UCalculateStr expr fn_out_dbl fn_out_str =>
                Some (MCalculateStr expr fn_out_dbl fn_out_str)
                *)
        | UHwRead fn =>
                do f_ty <- record_field_type rt fn ;;
                Some (MHwRead fn f_ty)
        | UHwWrite fn out_ty =>
                do f_ty <- record_field_type rt fn ;;
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
                do ol_rt <- lookup_type dbt (fl_rn ol) ;;
                do ol_ty <- record_field_type ol_rt (fl_fn ol) ;;
                Some (MHavocWrite ol ol_ty)
        | UHavocProcess fl => Some (MHavocProcess fl)
        end in go.


Definition compile_record dbt rc : option record_program :=
    let ucode := compile_record_untyped rc in
    let rt := record_config_type rc in
    map_opt (type_umicro dbt rt) ucode >>= fun code =>
    Some (RecordProgram rt code).

Definition compile_database dbc : option database_program :=
    let dbt := database_config_type dbc in
    map_opt (compile_record dbt) dbc.

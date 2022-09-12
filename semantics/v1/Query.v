Require Import Arith.
Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import Flocq.Appli.Fappli_IEEE_bits.
Require Import String.
Open Scope string.

Require Import v1.NeutronTactics.
Require Import v1.Util.
Require Import v1.Multi.
Require Import v1.Expr.
Require Import v1.ExprDbl.
Require Import v1.EpicsTypes.
Require Import v1.EpicsRecords.
Require Import v1.Step.
Require Import v1.StepAux.
Require Import v1.Terminate.
Require Import v1.Preservation.
Require Import v1.Wf.
Require Import v1.Interp.
Require Import v1.ListLemmas.
Require Import v1.Queue.
Require Import v1.System.
Require Import v1.SystemWf.
Open Scope nat.

(* Make the extracted code a little nicer. *)
Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellNatNum.
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellZNum.

Require v1.FloatAbsInt.

Set Default Timeout 10.



Record valid_state := mk_valid_state
    { vs_sys : system_state
    ; vs_sys_wf : system_state_wf vs_sys

    ; vs_dbc : database_config
    ; vs_dbu : database_uprogram
    ; vs_dbu_dbc : compile_database vs_dbc = vs_dbu
    ; vs_dbp_dbu : type_database_program vs_dbu = Some (sys_dbp vs_sys)
    }.


Definition decide_type_match : forall (dbt1 dbt2 : database_type),
    { dbt1 = dbt2 } + { dbt1 <> dbt2 }.
eapply list_eq_dec.
eapply record_type_eq_dec.
Defined.

Definition concat := fun xs => fold_left append xs "".
Definition join xs :=
    match xs with
    | [] => ""
    | x :: xs => append x (concat (map (fun s => append " " s) xs))
    end.

Fixpoint nat_to_string n :=
    match n with
    | 0 => "0"
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | 9 => "9"
    | 10 => "10"
    | 11 => "11"
    | 12 => "12"
    | S(S(S(S(S(S(S(S(S(S(S(S n'))))))))))) => append "12+" (nat_to_string n')
    end.

Definition field_name_string fn :=
    match fn with
    | f_VAL => "VAL"
    | f_PVAL => "PVAL"
    | f_OVAL => "OVAL"
    | f_SVAL => "SVAL"
    | f_OSV => "OSV"
    | f_AVAL => "AVAL"
    | f_OAV => "OAV"
    | f_A_to_L i => concat ["A..L["; nat_to_string (index_nat i); "]"]
    | f_AA_to_LL i => concat ["AA..LL["; nat_to_string (index_nat i); "]"]
    | f_DO1_to_DOA i => concat ["DO1..DOA["; nat_to_string (index_nat i); "]"]
    | f_PACT => "PACT"
    | f_PROC => "PROC"
    | f_tmp n => concat ["tmp["; nat_to_string n; "]"]
    (*| _ => "(bogus field name)"*)
    end.

Definition micro_string op :=
    join match op with
    | MSetConst fn _ => ["MSetConst"; field_name_string fn]
    | MCopy src _ dest _ => ["MCopy"; field_name_string src; field_name_string dest]
    | MReadLink _ _ fn _ => ["MReadLink"; field_name_string fn]
    | MWriteLink fn _ _ _ => ["MWriteLink"; field_name_string fn]
    | MProcess _ => ["MProcess"]
    | MCalculate _ fn => ["MCalculate"; field_name_string fn]
    | MCalculateStr _ fn_dbl fn_str =>
            ["MCalculateStr";
             field_name_string fn_dbl;
             field_name_string fn_str]
    | MHwWrite fn _ _ => ["MHwWrite"; field_name_string fn]
    | MCalcCond cur prev _ _ => ["MCalcCond"; field_name_string cur; field_name_string prev]
    | MScheduleCallback _ _ => ["MScheduleCallback"]
    | MCheckPACT => ["MCheckPACT"]
    | MHavocUpdate => ["MHavocUpdate"]
    | MHavocWrite _ _ => ["MHavocWrite"]
    | MHavocProcess _ => ["MHavocProcess"]
    end.

Definition record_type_string rt :=
    match rt with
    | RtCalc => "calc"
    | RtCalcOut => "calcout"
    | RtStrCalcOut => "scalcout"
    | RtArrayCalcOut _ => "acalcout"
    | RtFanout => "fanout"
    | RtDFanout => "dfanout"
    | RtSeq => "seq"
    | RtAnalogIn => "ai"
    | RtAnalogOut => "ao"
    | RtBinaryIn => "bi"
    | RtBinaryOut => "bo"
    | RtMBBO => "mbbo"
    | RtStringIn => "stringin"
    | RtStringOut => "stringout"
    | RtLongIn => "longin"
    | RtLongOut => "longout"
    | RtWaveform _ _ => "waveform"
    | RtSubarray _ _ _ => "subArray"
    | RtAsyn => "asyn"
    end.

Inductive error :=
| EWf (e : wf_error)
| ETy (e : type_error)
| ETime (e : option (list (record_name * nat * nat)))
| EMsg (msg : string)
.

Ltac die e := right; exact e.
Ltac die_msg msg := right; exact (EMsg msg).
Ltac die_auto := right; constructor; assumption.

Definition init_state : forall dbc dbs,
    { vs | vs_dbc vs = dbc /\ sys_dbs (vs_sys vs) = dbs } + error.
intros.

remember (compile_database dbc) as dbu.

destruct (type_database_program_with_check dbu) as [ dbp | ? ] eqn:?;
    [ | die_auto ].
on _, eapply_lem type_database_program_with_check_inl_eq.

remember (database_program_type dbp) as dbt.

destruct (check_wfm_database dbt dbp);
    [ | die_auto ].

destruct (check_database_time dbp) as [ [ dbm ? ] | ];
    [ | die (ETime (find_loops dbp)) ].

remember (database_state_type dbs) as dbt'.
destruct (list_eq_dec record_type_eq_dec dbt dbt');
    [ | die_msg "state and config types do not match" ].

remember ([] : list timestamped_event) as evts.

left.
simple refine (let sys : system_state := _ in _).
  { econstructor; (symmetry + idtac); eassumption. }
simple refine (let sys_wf : system_state_wf sys := _ in _).
  { econstructor; hide; subst; simpl in *;
      eauto using Sorted.SSorted_nil; try congruence. }
simple refine (let vs : valid_state := _ in _).
  { econstructor; (symmetry + idtac); eassumption. }
exists vs. split; simpl in *; congruence.
Defined.


Definition run_state (vs : valid_state) (now : time) :
    { vs', oes | vs_dbc vs = vs_dbc vs' /\
                 system_step now (vs_sys vs) (vs_sys vs') oes } +
            ~(exists evt, In evt (sys_evts (vs_sys vs)) /\ te_when evt <= now)%Z.
forward eapply (@interp_system_step now (vs_sys vs) (vs_sys_wf vs)) as HH.
destruct HH as [ [sys' oes Hstep] | err ];
    [ left | right; assumption ].

destruct vs; destruct vs_sys0; simpl in *.

simple refine (let sys'_wf : system_state_wf sys' := _ in _).
  { hide. eapply system_step_preserves_wf; eauto. }
simple refine (let vs' : valid_state := _ in _).
  { eapply (mk_valid_state sys' sys'_wf); hide; eauto.
    - inversion Hstep. subst. eauto. }
exists vs' oes; eauto.
Defined.


Definition field_read : forall vs rn fn,
    { val | read_record_field (sys_dbs (vs_sys vs)) rn fn = Some val } +
    { ~(exists ty, wfm_field_access (database_state_type (sys_dbs (vs_sys vs))) rn fn ty) }.
intros.
destruct (read_record_field _ rn fn) eqn:Heq.
- left. eexists. reflexivity.
- right. destruct 1 as [ty Hty].
  destruct vs, vs_sys0, vs_sys_wf0. subst. simpl in *.
  forward eapply interp_read_record_field as [val Hval]; eauto.
  break_and. congruence.
Defined.

Definition field_write : forall vs rn fn val,
    { vs' | vs_dbc vs = vs_dbc vs' /\
            write_record_field (sys_dbs (vs_sys vs)) rn fn val = Some (sys_dbs (vs_sys vs')) } +
    { ~wfm_field_access (database_state_type (sys_dbs (vs_sys vs))) rn fn (value_type val) }.
intros.
destruct (write_record_field _ rn fn val) as [ dbs' | ] eqn:Heq.

- left.
  destruct vs, vs_sys0. subst. simpl in *.
  simple refine (let sys' : system_state := _ in _).
    { refine (SystemState sys_dbp sys_dbm dbs' sys_evts). }
  simple refine (let sys'_wf : system_state_wf sys' := _ in _).
    { hide. destruct vs_sys_wf0.
      econstructor; subst; simpl in *; eauto;
      try solve [erewrite <- write_record_field_preserves_state_type; eauto]. }
  simple refine (let vs' : valid_state := _ in _).
    { eapply (mk_valid_state sys' sys'_wf); hide; eauto. }
  exists vs'. split; eauto.

- right. intro Hty.
  destruct vs, vs_sys0, vs_sys_wf0. subst. simpl in *.
  forward eapply interp_write_record_field as [dbs' Hdbs']; eauto.
  congruence.
Defined.

Definition enqueue_event (vs : valid_state) (when : time) (ie : input_event) :
    (* TODO: would be nice when `ie` is not well formed to include a proof of
       that fact, but we don't have a decider for that yet *)
    option { vs' | vs_dbc vs = vs_dbc vs' /\
                   insert_one (TsEvent when ie) (sys_evts (vs_sys vs)) (sys_evts (vs_sys vs')) }.
destruct (check_wfm_input_event (database_state_type (sys_dbs (vs_sys vs))) ie) as [Hwfie | ];
    [ | exact None ].
eapply Some.
destruct vs, vs_sys0. subst. simpl in *.

destruct (interp_insert_one_evt_sorted (TsEvent when ie) sys_evts) as (evts' & Hins & Hsort).

simple refine (let sys' : system_state :=
    SystemState sys_dbp sys_dbm sys_dbs evts'
    in _).
simple refine (let sys'_wf : system_state_wf sys' := _ in _).
  { hide. destruct vs_sys_wf0; simpl in *.
    econstructor; subst; simpl in *; eauto;
    try solve [erewrite <- write_record_field_preserves_state_type; eauto].
    - rewrite Forall_forall in *. intros.
      forward eapply insert_one_from as HH; eauto. destruct HH; eauto.
      subst. simpl. assumption. }
simple refine (let vs' : valid_state := _ in _).
  { eapply (mk_valid_state sys' sys'_wf); hide; eauto. }

exists vs'. split; eauto.
Defined.


Definition compile_dbp dbc :=
    let dbu := compile_database dbc in
    type_database_program_with_check dbu.


Extract Inductive FloatAbsInt.Abs.record_abs =>
    "Record_abs" [
        "RaCalc"
        "RaCalcOut"
        "RaStrCalcOut"
        "RaArrayCalcOut"
        "RaFanout"
        "RaAnalogIn"
        "RaAnalogOut"
        "RaBinaryIn"
        "RaBinaryOut"
        "RaMBBO"
        "RaStringIn"
        "RaStringOut"
        "RaLongIn"
        "RaLongOut"
        "RaDFanout"
        "RaSeq"
        "RaWaveform"
        "RaSubarray"
        "RaAsyn"
    ].

Extraction Language Haskell.
Extraction "Query.hs"
    (* types *)
    value in_link out_link fwd_link

    (* functions *)
    init_state run_state enqueue_event
    field_read field_write
    b64_opp b64_plus b64_minus b64_mult b64_div b64_sqrt
    b64_of_bits bits_of_b64
    multi_rep multi_get multi_set
    default_array
    LONG_MAX

    compile_dbp
    FloatAbsInt.float_abs_init
    FloatAbsInt.float_abs_update
    FloatAbsInt.float_abs_check
    .


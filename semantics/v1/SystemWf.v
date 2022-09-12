Require Import Arith.
Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import Sorted.
Require Import Omega.

Require Import v1.Step.
Require Import v1.System.
Require Import v1.Queue.
Require Import v1.NeutronTactics.
Require Import v1.Wf.
Require Import v1.Terminate.


Record system_state_wf sys : Prop := SystemStateWf
    { swf_dbt : database_type
    ; swf_dbt_dbs : database_state_type (sys_dbs sys) = swf_dbt
    ; swf_dbt_dbp : database_program_type (sys_dbp sys) = swf_dbt

    ; swf_dbm_dbp : database_time (sys_dbm sys) (sys_dbp sys)

    ; swf_wfm : wfm_database swf_dbt (sys_dbp sys)

    ; swf_evts_sorted : StronglySorted te_le (sys_evts sys)
    ; swf_evts_wfm : Forall (fun te => wfm_input_event swf_dbt (te_evt te)) (sys_evts sys)
    }.



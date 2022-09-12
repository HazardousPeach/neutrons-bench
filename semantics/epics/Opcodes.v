Require Import List.
Import ListNotations.

Require Export epics.SpecOpcodes.


Definition micro_rect_mut' (P : micro -> Type) (Pl : list micro -> Type)
        (HSetConst :    forall fn val,
            P (MSetConst fn val))
        (HCopy :        forall fn_src src_ty fn_dest dest_ty,
            P (MCopy fn_src src_ty fn_dest dest_ty))
        (HReadLink :    forall il il_ty fn f_ty,
            P (MReadLink il il_ty fn f_ty))
        (HWriteLink :   forall fn f_ty ol ol_ty,
            P (MWriteLink fn f_ty ol ol_ty))
        (HProcess :     forall fl,
            P (MProcess fl))
        (HCalculate :   forall expr fn_out,
            P (MCalculate expr fn_out))
            (*
        (HCalculateStr : forall expr fn_out_dbl fn_out_str,
            P (MCalculateStr expr fn_out_dbl fn_out_str))
            *)
        (HHwRead :      forall fn f_ty,
            P (MHwRead fn f_ty))
        (HHwWrite :     forall fn f_ty out_ty,
            P (MHwWrite fn f_ty out_ty))
        (HCalcCond :    forall fn_cur fn_prev oopt body,
            Pl body -> P (MCalcCond fn_cur fn_prev oopt body))
        (HScheduleCallback : forall delay code,
            Pl code -> P (MScheduleCallback delay code))
        (HCheckPACT :
            P (MCheckPACT))
        (HUnkRead :     forall fn f_ty,
            P (MUnkRead fn f_ty))
        (HUnkWrite :
            P (MUnkWrite))
        (HHavocUpdate :
            P (MHavocUpdate))
        (HHavocWrite :  forall ol ol_ty,
            P (MHavocWrite ol ol_ty))
        (HHavocProcess : forall fl,
            P (MHavocProcess fl))
        (Hnil :
            Pl [])
        (Hcons :        forall op ops,
            P op -> Pl ops -> Pl (op :: ops))
        : (forall op, P op) * (forall ops, Pl ops) :=

    let fix go op :=
        let fix go_list ops :=
            match ops as ops_ return Pl ops_ with
            | [] => Hnil
            | op :: ops => Hcons op ops (go op) (go_list ops)
            end in
        match op with
        | MSetConst fn val =>
                HSetConst fn val
        | MCopy fn_src src_ty fn_dest dest_ty =>
                HCopy fn_src src_ty fn_dest dest_ty
        | MReadLink il il_ty fn f_ty =>
                HReadLink il il_ty fn f_ty
        | MWriteLink fn f_ty ol ol_ty =>
                HWriteLink fn f_ty ol ol_ty
        | MProcess fl =>
                HProcess fl
        | MCalculate expr fn_out =>
                HCalculate expr fn_out
                (*
        | MCalculateStr expr fn_out_dbl fn_out_str =>
                HCalculateStr expr fn_out_dbl fn_out_str
                *)
        | MHwRead fn f_ty =>
                HHwRead fn f_ty
        | MHwWrite fn f_ty out_ty =>
                HHwWrite fn f_ty out_ty
        | MCalcCond fn_cur fn_prev oopt body =>
                HCalcCond fn_cur fn_prev oopt body (go_list body)
        | MScheduleCallback delay code =>
                HScheduleCallback delay code (go_list code)
        | MCheckPACT =>
                HCheckPACT
        | MUnkRead fn f_ty =>
                HUnkRead fn f_ty
        | MUnkWrite =>
                HUnkWrite
        | MHavocUpdate =>
                HHavocUpdate
        | MHavocWrite ol ol_ty =>
                HHavocWrite ol ol_ty
        | MHavocProcess fl =>
                HHavocProcess fl
        end in
    let fix go_list ops :=
        match ops as ops_ return Pl ops_ with
        | [] => Hnil
        | op :: ops => Hcons op ops (go op) (go_list ops)
        end in
    (go, go_list).

Definition micro_rect_mut (P : micro -> Type) (Pl : list micro -> Type)
        HSetConst HCopy HReadLink HWriteLink HProcess HCalculate (*HCalculateStr*)
        HHwRead HHwWrite HCalcCond HScheduleCallback HCheckPACT HUnkRead HUnkWrite
        HHavocUpdate HHavocWrite HHavocProcess Hnil Hcons
        : forall op, P op :=
    fst (micro_rect_mut' P Pl
    HSetConst HCopy HReadLink HWriteLink HProcess HCalculate (*HCalculateStr*)
    HHwRead HHwWrite HCalcCond HScheduleCallback HCheckPACT HUnkRead HUnkWrite
    HHavocUpdate HHavocWrite HHavocProcess Hnil Hcons).

Definition micro_ind' (P : micro -> Prop)
        HSetConst HCopy HReadLink HWriteLink HProcess HCalculate (*HCalculateStr*)
        HHwRead HHwWrite HCalcCond HScheduleCallback HCheckPACT HUnkRead HUnkWrite
        HHavocUpdate HHavocWrite HHavocProcess
        : forall op, P op :=
    micro_rect_mut P (Forall P)
    HSetConst HCopy HReadLink HWriteLink HProcess HCalculate (*HCalculateStr*)
    HHwRead HHwWrite HCalcCond HScheduleCallback HCheckPACT HUnkRead HUnkWrite
    HHavocUpdate HHavocWrite HHavocProcess
    ltac:(eauto) ltac:(eauto).


Definition umicro_rect_mut' (P : umicro -> Type) (Pl : list umicro -> Type)
        (HSetConst : forall fn val,
            P (USetConst fn val))
        (HCopy : forall fn_src fn_dest,
            P (UCopy fn_src fn_dest))
        (HReadLink : forall il fn,
            P (UReadLink il fn))
        (HWriteLink : forall fn ol,
            P (UWriteLink fn ol))
        (HWriteLinkTyped : forall fns ol,
            P (UWriteLinkTyped fns ol))
        (HProcess : forall fl,
            P (UProcess fl))
        (HCalculate : forall expr fn_out,
            P (UCalculate expr fn_out))
            (*
        (HCalculateStr : forall expr fn_out_dbl fn_out_str,
            P (UCalculateStr expr fn_out_dbl fn_out_str))
            *)
        (HHwRead : forall fn,
            P (UHwRead fn))
        (HHwWrite : forall fn out_ty,
            P (UHwWrite fn out_ty))
        (HCalcCond : forall fn_cur fn_prev oopt body,
            Pl body -> P (UCalcCond fn_cur fn_prev oopt body))
        (HScheduleCallback : forall delay code,
            Pl code -> P (UScheduleCallback delay code))
        (HCheckPACT :
            P (UCheckPACT))
        (HHavocUpdate :
            P (UHavocUpdate))
        (HHavocWrite : forall ol,
            P (UHavocWrite ol))
        (HHavocProcess : forall fl,
            P (UHavocProcess fl))
        (Hnil :
            Pl [])
        (Hcons :        forall op ops,
            P op -> Pl ops -> Pl (op :: ops))
        : (forall op, P op) * (forall ops, Pl ops) :=

    let fix go op :=
        let fix go_list ops :=
            match ops as ops_ return Pl ops_ with
            | [] => Hnil
            | op :: ops => Hcons op ops (go op) (go_list ops)
            end in
        match op with
        | USetConst fn val =>
                HSetConst fn val
        | UCopy fn_src fn_dest =>
                HCopy fn_src fn_dest
        | UReadLink il fn =>
                HReadLink il fn
        | UWriteLink fn ol =>
                HWriteLink fn ol
        | UWriteLinkTyped fns ol =>
                HWriteLinkTyped fns ol
        | UProcess fl =>
                HProcess fl
        | UCalculate expr fn_out =>
                HCalculate expr fn_out
                (*
        | UCalculateStr expr fn_out_dbl fn_out_str =>
                HCalculateStr expr fn_out_dbl fn_out_str
                *)
        | UHwRead fn =>
                HHwRead fn
        | UHwWrite fn out_ty =>
                HHwWrite fn out_ty
        | UCalcCond fn_cur fn_prev oopt body =>
                HCalcCond fn_cur fn_prev oopt body (go_list body)
        | UScheduleCallback delay code =>
                HScheduleCallback delay code (go_list code)
        | UCheckPACT =>
                HCheckPACT
        | UHavocUpdate =>
                HHavocUpdate
        | UHavocWrite ol =>
                HHavocWrite ol
        | UHavocProcess fl =>
                HHavocProcess fl
        end in
    let fix go_list ops :=
        match ops as ops_ return Pl ops_ with
        | [] => Hnil
        | op :: ops => Hcons op ops (go op) (go_list ops)
        end in
    (go, go_list).


Definition umicro_rect_mut (P : umicro -> Type) (Pl : list umicro -> Type)
        HSetConst HCopy HReadLink HWriteLink HWriteLinkTyped HProcess
            HCalculate (*HCalculateStr*)
        HHwRead HHwWrite HCalcCond HScheduleCallback HCheckPACT
        HHavocUpdate HHavocWrite HHavocProcess Hnil Hcons
        : forall op, P op :=
    fst (umicro_rect_mut' P Pl
    HSetConst HCopy HReadLink HWriteLink HWriteLinkTyped HProcess
        HCalculate (*HCalculateStr*)
    HHwRead HHwWrite HCalcCond HScheduleCallback HCheckPACT
    HHavocUpdate HHavocWrite HHavocProcess Hnil Hcons).


Definition record_program_type := rp_type.
Definition database_program_type dbp :=
    map record_program_type dbp.


Inductive MicroForall (P : micro -> Prop) : micro -> Prop:=
| MfCalcCond : forall fn_cur fn_prev oopt body,
        P (MCalcCond fn_cur fn_prev oopt body) ->
        Forall (MicroForall P) body ->
        MicroForall P (MCalcCond fn_cur fn_prev oopt body)
| MfScheduleCallback : forall delay code,
        P (MScheduleCallback delay code) ->
        Forall (MicroForall P) code ->
        MicroForall P (MScheduleCallback delay code)
| MfOther : forall op,
        match op with
        | MCalcCond _ _ _ _ => False
        | MScheduleCallback _ _ => False
        | _ => True
        end ->
        P op ->
        MicroForall P op.

Lemma forall_one : forall P op,
    MicroForall P op ->
    P op.
inversion 1; auto.
Qed.


Definition is_db_op (op : micro) :=
    match op with
    | MSetConst _ _ => true
    | MCopy _ _ _ _ => true
    | MReadLink _ _ _ _ => true
    | MWriteLink _ _ _ _ => true
    | MCalculate _ _ => true
    | MHwRead _ _ => true
    | MUnkRead _ _ => true
    | MUnkWrite => true
    | MHavocUpdate => true
    | MHavocWrite _ _ => true
    | _ => false
    end.

Definition is_output_op (op : micro) :=
    match op with
    | MHwWrite _ _ _ => true
    | MScheduleCallback _ _ => true
    | _ => false
    end.


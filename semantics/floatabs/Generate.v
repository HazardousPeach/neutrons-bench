Require Import Arith.
Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import Sorted.
Require Import Omega.
Require Import Psatz.

Require Import v1.FloatAux.
Require Import v1.Multi.
Require Import v1.Util.

Require Import epics.Opcodes.
Require Import epics.Records.
Require Import epics.Types.
Require floatabs.AbsExpr.
Require Import floatabs.Records.
Require Import util.ListLemmas.


Module Abs := floatabs.Records.


Set Default Timeout 10.


(* building the initial state *)

Definition double_abs (d : e_double) : abs_value :=
    match B2Z_safe d with
    | Some x => Some (x, x)
    | None => None
    end.

Definition enum_abs (e : e_enum) : abs_value :=
    let '(EEnum val _) := e in
    Some (val, val).

Definition long_abs (e : e_long) : abs_value :=
    let '(ELong val _) := e in
    Some (val, val).

Definition value_abs (v : value) : abs_value :=
    match v with
    | VDouble d => double_abs d
    | VEnum e => enum_abs e
    | VLong l => long_abs l
    | _ => None
    end.

Definition record_state_abs s :=
    match s with
    | RsCalc (CalcState a2l val) => 
            RaCalc (CalcAbs
                (multi_map double_abs a2l)
                (double_abs val))
    | RsCalcOut (CalcOutState a2l val pval oval tmp0) => 
            RaCalcOut (CalcOutAbs
                (multi_map double_abs a2l)
                (double_abs val)
                (double_abs pval)
                (double_abs oval)
                (double_abs tmp0))
    | RsStrCalcOut (StrCalcOutState a2l _ val _ pval oval _ tmp0) =>
            RaStrCalcOut (StrCalcOutAbs
                (multi_map double_abs a2l)
                (double_abs val)
                (double_abs pval)
                (double_abs oval)
                (double_abs tmp0))
    | RsArrayCalcOut n (ArrayCalcOutState _ a2l _ val _ pval oval _ tmp0) =>
            RaArrayCalcOut _ (ArrayCalcOutAbs n
                (multi_map double_abs a2l)
                (double_abs val)
                (double_abs pval)
                (double_abs oval)
                (double_abs tmp0))
    | RsFanout (FanoutState) =>
            RaFanout (FanoutAbs)
    | RsAnalogIn (AnalogInState val) =>
            RaAnalogIn (AnalogInAbs
                (double_abs val))
    | RsAnalogOut (AnalogOutState val pval) =>
            RaAnalogOut (AnalogOutAbs
                (double_abs val)
                (double_abs pval))
    | RsBinaryIn (BinaryInState val) =>
            RaBinaryIn (BinaryInAbs
                (enum_abs val))
    | RsBinaryOut (BinaryOutState val) =>
            RaBinaryOut (BinaryOutAbs
                (enum_abs val))
    | RsMBBO (MBBOState val) =>
            RaMBBO (MBBOAbs
                (enum_abs val))
    | RsStringIn (StringInState _) =>
            RaStringIn (StringInAbs)
    | RsStringOut (StringOutState _) =>
            RaStringOut (StringOutAbs)
    | RsLongIn (LongInState val) =>
            RaLongIn (LongInAbs
                (long_abs val))
    | RsLongOut (LongOutState val) =>
            RaLongOut (LongOutAbs
                (long_abs val))
    | RsDFanout (DFanoutState val) =>
            RaDFanout (DFanoutAbs
                (double_abs val))
    | RsSeq (SeqState do1_to_a _) =>
            RaSeq (SeqAbs
                (multi_map double_abs do1_to_a))
    | RsWaveform ty n (WaveformState _ _ val) =>
            RaWaveform _ _ (WaveformAbs ty n)
    | RsSubarray ty n m (SubarrayState _ _ _ val tmp0) =>
            RaSubarray _ _ _ (SubarrayAbs ty n m)
    | RsAsyn (AsynState) =>
            RaAsyn (AsynAbs)
    end.

Definition database_state_abs (dbs : database_state) : database_abs :=
    map record_state_abs dbs.



(* update helpers *)

Definition merge abs1 abs2 :=
    match abs1, abs2 with
    | Some (min1, max1), Some (min2, max2) =>
            Some (Z.min min1 min2, Z.max max1 max2)
    | _, _ => None
    end.

Definition merge_field ra fn abs :=
    Abs.read_field ra fn >>= fun abs' =>
    Abs.write_field ra fn (merge abs abs').

Definition merge_record_field dba rn fn abs :=
    Abs.update_record (fun ra => merge_field ra fn abs) dba rn.


Definition havoc_abs a :=
    match a with
    | RaCalc (CalcAbs _ _) => 
            RaCalc (CalcAbs (multi_rep 12 None) None)
    | RaCalcOut (CalcOutAbs _ _ _ _ _) => 
            RaCalcOut (CalcOutAbs (multi_rep 12 None) None None None None)
    | RaStrCalcOut (StrCalcOutAbs _ _ _ _ _) => 
            RaStrCalcOut (StrCalcOutAbs (multi_rep 12 None) None None None None)
    | RaArrayCalcOut n (ArrayCalcOutAbs _ _ _ _ _ _) => 
            RaArrayCalcOut _ (ArrayCalcOutAbs n (multi_rep 12 None) None None None None)
    | RaFanout (FanoutAbs) =>
            RaFanout (FanoutAbs)
    | RaAnalogIn (AnalogInAbs _) =>
            RaAnalogIn (AnalogInAbs None)
    | RaAnalogOut (AnalogOutAbs _ _) =>
            RaAnalogOut (AnalogOutAbs None None)
    | RaBinaryIn (BinaryInAbs _) =>
            RaBinaryIn (BinaryInAbs None)
    | RaBinaryOut (BinaryOutAbs _) =>
            RaBinaryOut (BinaryOutAbs None)
    | RaMBBO (MBBOAbs _) =>
            RaMBBO (MBBOAbs None)
    | RaStringIn (StringInAbs) =>
            RaStringIn (StringInAbs)
    | RaStringOut (StringOutAbs) =>
            RaStringOut (StringOutAbs)
    | RaLongIn (LongInAbs _) =>
            RaLongIn (LongInAbs None)
    | RaLongOut (LongOutAbs _) =>
            RaLongOut (LongOutAbs None)
    | RaDFanout (DFanoutAbs _) =>
            RaDFanout (DFanoutAbs None)
    | RaSeq (SeqAbs _) =>
            RaSeq (SeqAbs (multi_rep 10 None))
    | RaWaveform ty n (WaveformAbs _ _) =>
            RaWaveform _ _ (WaveformAbs ty n)
    | RaSubarray ty n m (SubarrayAbs _ _ _) =>
            RaSubarray _ _ _ (SubarrayAbs ty n m)
    | RaAsyn (AsynAbs) =>
            RaAsyn (AsynAbs)
    end.

Definition clamp_abs low high abs :=
    match abs with
    | Some (low', high') =>
            let low'' := Z.max low low' in
            let high'' := Z.min high high' in
            Some (low'', high'')
    | None => None
    end.



(* update functions *)

Definition interp_convert abs new_ty :=
    (* TODO probably needs some updating *)
    match new_ty with
    | TDouble => abs
    | TLong => clamp_abs (-LONG_MAX) (LONG_MAX - 1) abs
    | TEnum => clamp_abs 0 (ENUM_MAX - 1) abs
    | _ => None
    end.

Definition interp_set_const dba rn fn val :=
    let abs := value_abs val in
    merge_record_field dba rn fn abs.

Definition interp_copy dba rn fn_src (src_ty : field_type) fn_dest dest_ty :=
    let f ra :=
        Abs.read_field ra fn_src >>= fun abs =>
        let abs' := interp_convert abs dest_ty in
        merge_field ra fn_dest abs' in
    Abs.update_record f dba rn.

Definition interp_read_link dba rn il (il_ty : field_type) fn f_ty :=
    Abs.read_record_field dba (fl_rn il) (fl_fn il) >>= fun abs =>
    let abs' := interp_convert abs f_ty in
    merge_record_field dba rn fn abs'.

Definition interp_write_link dba rn fn (f_ty : field_type) ol ol_ty :=
    Abs.read_record_field dba rn fn >>= fun abs =>
    let abs' := interp_convert abs ol_ty in
    merge_record_field dba (fl_rn ol) (fl_fn ol) abs'.

Definition interp_calculate dba rn e fn_out :=
    lookup dba rn >>= fun ra =>
    floatabs.AbsExpr.denote e >>= fun f =>
    match ra with
    | RaCalc (CalcAbs a2l val) =>
            let (a2l', result) := f a2l in
            let a2l'' := multi_zip merge a2l a2l' in
            Some (RaCalc (CalcAbs a2l'' val), result)
    | RaCalcOut (CalcOutAbs a2l val pval oval tmp0) =>
            let (a2l', result) := f a2l in
            let a2l'' := multi_zip merge a2l a2l' in
            Some (RaCalcOut (CalcOutAbs a2l'' val pval oval tmp0), result)
    | _ => None
    end >>= fun x => let '(ra', result) := x in
    merge_field ra' fn_out result >>= fun ra'' =>
    Abs.update_record (fun _ => Some ra'') dba rn.

Definition interp_havoc_update dba rn :=
    Abs.update_record (fun ra => Some (havoc_abs ra)) dba rn.

Definition interp_hw_read dba rn fn (f_ty : field_type) :=
    merge_record_field dba rn fn None.

Definition interp_unk_read dba rn fn (f_ty : field_type) :=
    merge_record_field dba rn fn None.

Definition interp_unk_write (dba : database_abs) (rn : record_name) :=
    Some dba.

Definition interp_havoc_write dba (rn : record_name) ol (ol_ty : field_type) :=
    merge_record_field dba (fl_rn ol) (fl_fn ol) None.

Definition interp_op dba rn op :=
    match op with
    | MSetConst fn val =>
            interp_set_const dba rn fn val
    | MCopy fn_src src_ty fn_dest dest_ty =>
            interp_copy dba rn fn_src src_ty fn_dest dest_ty
    | MReadLink il il_ty fn f_ty =>
            interp_read_link dba rn il il_ty fn f_ty
    | MWriteLink fn f_ty ol ol_ty =>
            interp_write_link dba rn fn f_ty ol ol_ty
    | MCalculate expr fn_out =>
            interp_calculate dba rn expr fn_out
    | MHwRead fn f_ty =>
            interp_hw_read dba rn fn f_ty
    | MUnkRead fn f_ty =>
            interp_unk_read dba rn fn f_ty
    | MUnkWrite =>
            interp_unk_write dba rn
    | MHavocUpdate =>
            interp_havoc_update dba rn
    | MHavocWrite ol ol_ty =>
            interp_havoc_write dba rn ol ol_ty
    | _ => Some dba
    end.

Definition interp_op_rec rn :=
    let fix go dba op :=
        let fix go_list dba ops :=
            match ops with
            | [] => Some dba
            | op :: ops => go dba op >>= fun dba => go_list dba ops
            end in
        interp_op dba rn op >>= fun dba =>
        match op with
        | MCalcCond _ _ _ body => go_list dba body
        | MScheduleCallback _ code => go_list dba code
        | _ => Some dba
        end in go.

Definition interp_op_rec_list rn :=
    let go := interp_op_rec rn in
    let fix go_list dba ops :=
        match ops with
        | [] => Some dba
        | op :: ops => go dba op >>= fun dba => go_list dba ops
        end in go_list.

Definition interp_ops dba rn ops := interp_op_rec_list rn dba ops.

Definition interp_prog dba dbp :=
    let fix go dba xs :=
        match xs with
        | [] => Some dba
        | (rn, rp) :: xs =>
            interp_ops dba rn (rp_code rp) >>= fun dba =>
            go dba xs
        end in
    go dba (numbered dbp).



(* overapproximate any fields that are still changing *)

Definition abs_value_eq_dec (x y : abs_value) : { x = y } + { x <> y }.
decide equality. decide equality; auto using Z.eq_dec.
Qed.

Definition truncate_abs abs1 abs2 :=
    if abs_value_eq_dec abs1 abs2 then abs1 else None.

Definition truncate_record ra1 ra2 :=
    let f := truncate_abs in
    match ra1, ra2 with
    | RaCalc (CalcAbs a1 b1),
      RaCalc (CalcAbs a2 b2) =>
      Some (RaCalc (CalcAbs
        (multi_zip f a1 a2) (f b1 b2)))
    | RaCalcOut (CalcOutAbs a1 b1 c1 d1 e1),
      RaCalcOut (CalcOutAbs a2 b2 c2 d2 e2) =>
      Some (RaCalcOut (CalcOutAbs
        (multi_zip f a1 a2) (f b1 b2) (f c1 c2) (f d1 d2) (f e1 e2)))
    | RaStrCalcOut (StrCalcOutAbs a1 b1 c1 d1 e1),
      RaStrCalcOut (StrCalcOutAbs a2 b2 c2 d2 e2) =>
      Some (RaStrCalcOut (StrCalcOutAbs
        (multi_zip f a1 a2) (f b1 b2) (f c1 c2) (f d1 d2) (f e1 e2)))
    | RaArrayCalcOut n1 (ArrayCalcOutAbs _ a1 b1 c1 d1 e1),
      RaArrayCalcOut n2 (ArrayCalcOutAbs _ a2 b2 c2 d2 e2) =>
      (if eq_nat_dec n1 n2 then Some n1 else None) >>= fun n =>
      Some (RaArrayCalcOut n (ArrayCalcOutAbs n
        (multi_zip f a1 a2) (f b1 b2) (f c1 c2) (f d1 d2) (f e1 e2)))

    | RaFanout (FanoutAbs),
      RaFanout (FanoutAbs) =>
      Some (RaFanout (FanoutAbs))

    | RaAnalogIn (AnalogInAbs a1),
      RaAnalogIn (AnalogInAbs a2) =>
      Some (RaAnalogIn (AnalogInAbs
        (f a1 a2)))
    | RaAnalogOut (AnalogOutAbs a1 b1),
      RaAnalogOut (AnalogOutAbs a2 b2) =>
      Some (RaAnalogOut (AnalogOutAbs
        (f a1 a2) (f b1 b2)))
    | RaBinaryIn (BinaryInAbs a1),
      RaBinaryIn (BinaryInAbs a2) =>
      Some (RaBinaryIn (BinaryInAbs
        (f a1 a2)))
    | RaBinaryOut (BinaryOutAbs a1),
      RaBinaryOut (BinaryOutAbs a2) =>
      Some (RaBinaryOut (BinaryOutAbs
        (f a1 a2)))
    | RaMBBO (MBBOAbs a1),
      RaMBBO (MBBOAbs a2) =>
      Some (RaMBBO (MBBOAbs
        (f a1 a2)))
    | RaStringIn (StringInAbs),
      RaStringIn (StringInAbs) =>
      Some (RaStringIn (StringInAbs))
    | RaStringOut (StringOutAbs),
      RaStringOut (StringOutAbs) =>
      Some (RaStringOut (StringOutAbs))
    | RaLongIn (LongInAbs a1),
      RaLongIn (LongInAbs a2) =>
      Some (RaLongIn (LongInAbs
        (f a1 a2)))
    | RaLongOut (LongOutAbs a1),
      RaLongOut (LongOutAbs a2) =>
      Some (RaLongOut (LongOutAbs
        (f a1 a2)))

    | RaDFanout (DFanoutAbs a1),
      RaDFanout (DFanoutAbs a2) =>
      Some (RaDFanout (DFanoutAbs
        (f a1 a2)))
    | RaSeq (SeqAbs a1),
      RaSeq (SeqAbs a2) =>
      Some (RaSeq (SeqAbs
        (multi_zip f a1 a2)))

    | RaWaveform ty1 n1 (WaveformAbs _ _),
      RaWaveform ty2 n2 (WaveformAbs _ _) =>
      (if elem_type_eq_dec ty1 ty2 then Some ty2 else None) >>= fun ty =>
      (if eq_nat_dec n1 n2 then Some n2 else None) >>= fun n =>
      Some (RaWaveform ty n (WaveformAbs ty n))
    | RaSubarray ty1 n1 m1 (SubarrayAbs _ _ _),
      RaSubarray ty2 n2 m2 (SubarrayAbs _ _ _) =>
      (if elem_type_eq_dec ty1 ty2 then Some ty2 else None) >>= fun ty =>
      (if eq_nat_dec n1 n2 then Some n2 else None) >>= fun n =>
      (if eq_nat_dec m1 m2 then Some m2 else None) >>= fun m =>
      Some (RaSubarray ty n m (SubarrayAbs ty n m))

    | RaAsyn (AsynAbs),
      RaAsyn (AsynAbs) =>
      Some (RaAsyn (AsynAbs))

    | _, _ => None
    end.

Fixpoint truncate_database dba1 dba2 :=
    match dba1, dba2 with
    | [], [] => Some []
    | ra1 :: dba1, ra2 :: dba2 =>
            truncate_record ra1 ra2 >>= fun ra =>
            truncate_database dba1 dba2 >>= fun dba =>
            Some (ra :: dba)
    | _, _ => None
    end.


(* field overrides *)

Definition override := (record_name, field_name, abs_value).

Definition apply_override dba override :=
    let '(rn, fn, abs) := override in
    match Abs.write_record_field dba rn fn abs with
    | Some dba' => dba'
    | None => dba
    end.

Fixpoint apply_overrides dba overrides :=
    match overrides with
    | [] => dba
    | ov :: ovs =>
            (* Apply in the order they appear in the list. *)
            let dba' := apply_override dba ov in
            apply_overrides dba' ovs
    end.




(* entry points *)

Definition float_abs_init (dbs : database_state) : database_abs :=
    database_state_abs dbs.

Definition float_abs_update dbp dba :=
    interp_prog dba dbp.

Definition float_abs_truncate dba1 dba2 :=
    truncate_database dba1 dba2.

Definition float_abs_apply_overrides dba overrides :=
    apply_overrides dba overrides.


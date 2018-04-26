module V = Val
module T = Tm

type el = V.can V.t
type tm = T.chk T.t

let rec equiv n ~ty el0 el1 =
  match V.out ty, V.out el0, V.out el1 with
  | _, V.Pi (dom0, cod0), V.Pi (dom1, cod1) ->
    let vdom0 = V.eval_clo dom0 in
    let vdom1 = V.eval_clo dom1 in
    let qdom = equiv n ~ty vdom0 vdom1 in
    let vgen0 = V.generic vdom0 n in
    let vgen1 = V.generic vdom1 n in
    let vcod0 = V.inst_bclo cod0 vgen0 in
    let vcod1 = V.inst_bclo cod1 vgen1 in
    let qcod = equiv (n+1) ~ty vcod0 vcod1 in
    T.pi None qdom qcod

  | _, V.Sg (dom0, cod0), V.Sg (dom1, cod1) ->
    let vdom0 = V.eval_clo dom0 in
    let vdom1 = V.eval_clo dom1 in
    let qdom = equiv n ~ty vdom0 vdom1 in
    let vgen0 = V.generic vdom0 n in
    let vgen1 = V.generic vdom1 n in
    let vcod0 = V.inst_bclo cod0 vgen0 in
    let vcod1 = V.inst_bclo cod1 vgen1 in
    let qcod = equiv (n+1) ~ty vcod0 vcod1 in
    T.sg None qdom qcod

  | _, V.Ext (cod0, sys0), V.Ext (cod1, sys1) ->
    let interval = V.into V.Interval in
    let vgen = V.generic interval n in
    let vcod0 = V.inst_bclo cod0 vgen in
    let vcod1 = V.inst_bclo cod1 vgen in
    let qcod = equiv (n+1) ~ty vcod0 vcod1 in
    let dimx = V.project_dimval vgen in
    let sys0x = V.inst_sclo sys0 dimx in
    let sys1x = V.inst_sclo sys1 dimx in
    let qsys = equiv_sys (n+1) ~ty:vcod0 sys0x sys1x in
    T.into @@ T.Ext (T.B (None, (qcod, qsys)))


  | _, V.Interval, V.Interval ->
    T.into T.Interval

  | _, V.Bool, V.Bool ->
    T.into T.Bool

  | _, V.Univ l0, V.Univ l1 ->
    if l0 = l1 then
      T.univ l0
    else
      failwith "equiv: univ level mismatch"

  | _, V.Tt, V.Tt ->
    T.into T.Tt

  | _, V.Ff, V.Ff ->
    T.into T.Ff

  | _, V.Coe coe0, V.Coe coe1 ->
    let interval = V.into V.Interval in
    let qdim0 = equiv_dim n coe0.dim0 coe0.dim0 in
    let qdim1 = equiv_dim n coe0.dim1 coe0.dim1 in
    let vgen = V.generic interval n in
    let vty0x = V.inst_bclo coe0.ty vgen in
    let vty1x = V.inst_bclo coe1.ty vgen in
    let qty = equiv_ty (n + 1) vty0x vty1x in
    let vty00 = V.inst_bclo coe0.ty @@ V.embed_dimval coe0.dim0 in
    let qtm = equiv n ~ty:vty00 coe0.tm coe1.tm in
    let tcoe = T.into @@ T.Coe {dim0 = qdim0; dim1 = qdim1; ty = T.B (None, qty); tm = qtm} in
    T.up tcoe

  | _, V.HCom {proj = Some v; _}, _ ->
    equiv n ~ty v el1

  | _, _, V.HCom {proj = Some v; _} ->
    equiv n ~ty el0 v

  | _, V.HCom hcom0, V.HCom hcom1 ->
    let qdim0 = equiv_dim n hcom0.dim0 hcom1.dim0 in
    let qdim1 = equiv_dim n hcom0.dim1 hcom1.dim1 in
    let vty0 = hcom0.ty in
    let vty1 = hcom1.ty in
    let qty = equiv_ty n vty0 vty1 in
    let qcap = equiv n ~ty:vty0 hcom0.cap hcom1.cap in
    let qsys = equiv_bsys n ~ty hcom0.sys hcom1.sys in
    let thcom = T.into @@ T.HCom {dim0 = qdim0; dim1 = qdim1; ty = qty; cap = qcap; sys = qsys} in
    T.up thcom

  | _, V.FCom {proj = Some v; _}, _ ->
    equiv n ~ty v el1

  | _, _, V.FCom {proj = Some v; _} ->
    equiv n ~ty el0 v

  | _, V.FCom _, V.FCom _ ->
    failwith "I haven't yet implemented quoting of fcom"

  | _, V.Up (_, neu0), V.Up (_, neu1) ->
    T.up @@ equiv_neu n neu0 neu1

  | _, V.Dim0, V.Dim0 ->
    T.into T.Dim0

  | _ , V.Dim1, V.Dim1 ->
    T.into T.Dim1

  | V.Pi (dom, cod), _, _ ->
    let vdom = V.eval_clo dom in
    let vgen = V.generic vdom n in
    let vcod = V.inst_bclo cod vgen in
    let vapp0 = V.apply el0 vgen in
    let vapp1 = V.apply el1 vgen in
    let qbdy = equiv (n + 1) ~ty:vcod vapp0 vapp1 in
    T.lam None qbdy

  | V.Ext (cod, _sys), _, _ ->
    let interval = V.into V.Interval in
    let vgen = V.generic interval n in
    let vdim = V.project_dimval vgen in
    let vcod = V.inst_bclo cod vgen in
    let vapp0 = V.ext_apply el0 vdim in
    let vapp1 = V.ext_apply el1 vdim in
    let qbdy = equiv (n+1) ~ty:vcod vapp0 vapp1 in
    T.lam None qbdy

  | V.Sg (dom, cod), _, _->
    let vdom = V.eval_clo dom in
    let vcar0 = V.car el0 in
    let vcar1 = V.car el1 in
    let vcdr0 = V.cdr el0 in
    let vcdr1 = V.cdr el1 in
    let vcod = V.inst_bclo cod vcar0 in
    let qcar = equiv n ~ty:vdom vcar0 vcar1 in
    let qcdr = equiv n ~ty:vcod vcdr0 vcdr1 in
    T.cons qcar qcdr

  | _ ->
    failwith "equiv"

and equiv_neu n neu0 neu1 =
  match V.out neu0, V.out neu1 with
  | V.Lvl l0, V.Lvl l1 ->
    if l0 != l1 then failwith "de bruijn level mismatch" else
      let ix = n - (l0 + 1) in
      T.var ix

  | V.FunApp (neu0, nfarg0), V.FunApp (neu1, nfarg1) ->
    let quo = equiv_neu n neu0 neu1 in
    let vdom, varg0 = V.out_nf nfarg0 in
    let _, varg1 = V.out_nf nfarg1 in
    let qarg = equiv n ~ty:vdom varg0 varg1 in
    T.into @@ T.FunApp (quo, qarg)

  | V.ExtApp (neu0, dim0), V.ExtApp (neu1, dim1) ->
    let quo = equiv_neu n neu0 neu1 in
    let qarg = equiv_dim n dim0 dim1 in
    T.into @@ T.ExtApp (quo, qarg)

  | V.Car neu0, V.Car neu1 ->
    T.car @@ equiv_neu n neu0 neu1

  | V.Cdr neu0, V.Cdr neu1 ->
    T.cdr @@ equiv_neu n neu0 neu1

  | V.If if0, V.If if1 ->
    let bool = V.into V.Bool in
    let vgen = V.generic bool n in
    let xmot0 = V.inst_bclo if0.mot vgen in
    let xmot1 = V.inst_bclo if1.mot vgen in
    let qmot = equiv_ty (n+1) xmot0 xmot1 in
    let qscrut = equiv_neu n if0.scrut if1.scrut in
    let tt = V.into V.Tt in
    let ff = V.into V.Ff in
    let tmot = V.inst_bclo if0.mot tt in
    let fmot = V.inst_bclo if1.mot ff in
    let tcase0 = V.eval_clo if0.tcase in
    let tcase1 = V.eval_clo if1.tcase in
    let qtcase = equiv n ~ty:tmot tcase0 tcase1 in
    let fcase0 = V.eval_clo if0.fcase in
    let fcase1 = V.eval_clo if1.fcase in
    let qfcase = equiv n ~ty:fmot fcase0 fcase1 in
    T.into @@ T.If {mot = T.B (None, qmot); scrut = qscrut; tcase = qtcase; fcase = qfcase}

  | _ -> failwith "equiv_neu"


and equiv_ty n ty0 ty1 =
  let univ = V.into @@ V.Univ Lvl.Omega in
  equiv n ~ty:univ ty0 ty1

and equiv_dim n dim0 dim1 =
  let interval = V.into V.Interval in
  equiv n ~ty:interval (V.embed_dimval dim0) (V.embed_dimval dim1)

and equiv_sys n ~ty sys0 sys1 =
  let rec go sys0 sys1 acc =
    match sys0, sys1 with
    | [], [] ->
      List.rev acc

    | V.Tube.Delete :: sys0, _ ->
      go sys0 sys1 acc

    | _, V.Tube.Delete :: sys1 ->
      go sys0 sys1 acc

    | V.Tube.True ((d00, d01), clo0) :: sys0, V.Tube.True ((d10, d11), clo1) :: sys1 ->
      let v0 = V.eval_clo clo0 in
      let v1 = V.eval_clo clo1 in
      let qd0 = equiv_dim n d00 d10 in
      let qd1 = equiv_dim n d01 d11 in
      let q = equiv n ~ty v0 v1 in
      let tb = qd0, qd1, Some q in
      go sys0 sys1 @@ tb :: acc

    | V.Tube.Indeterminate ((d00, d01), clo0) :: sys0, V.Tube.Indeterminate ((d10, d11), clo1) :: sys1 ->
      let v0 = V.eval_clo clo0 in
      let v1 = V.eval_clo clo1 in
      let qd0 = equiv_dim n d00 d10 in
      let qd1 = equiv_dim n d01 d11 in
      let q = equiv n ~ty v0 v1 in
      let tb = qd0, qd1, Some q in
      go sys0 sys1 @@ tb :: acc

    | V.Tube.False (d00, d01) :: sys0, V.Tube.False (d10, d11) :: _sys ->
      let qd0 = equiv_dim n d00 d10 in
      let qd1 = equiv_dim n d01 d11 in
      let tb = qd0, qd1, None in
      go sys0 sys1 @@ tb :: acc

    | _ -> failwith "equiv_sys"
  in
  go sys0 sys1 []


and equiv_bsys n ~ty sys0 sys1 =
  let interval = V.into V.Interval in
  let rec go sys0 sys1 acc =
    match sys0, sys1 with
    | [], [] ->
      List.rev acc

    | V.Tube.Delete :: sys0, _ ->
      go sys0 sys1 acc

    | _, V.Tube.Delete :: sys1 ->
      go sys0 sys1 acc

    | V.Tube.True ((d00, d01), clo0) :: sys0, V.Tube.True ((d10, d11), clo1) :: sys1 ->
      let vgen = V.generic interval n in
      let v0 = V.inst_bclo clo0 vgen in
      let v1 = V.inst_bclo clo1 vgen in
      let qd0 = equiv_dim n d00 d10 in
      let qd1 = equiv_dim n d01 d11 in
      let q = equiv (n+1) ~ty v0 v1 in
      let tb = qd0, qd1, Some (T.B (None, q)) in
      go sys0 sys1 @@ tb :: acc

    | V.Tube.Indeterminate ((d00, d01), clo0) :: sys0, V.Tube.Indeterminate ((d10, d11), clo1) :: sys1 ->
      let vgen = V.generic interval n in
      let v0 = V.inst_bclo clo0 vgen in
      let v1 = V.inst_bclo clo1 vgen in
      let qd0 = equiv_dim n d00 d10 in
      let qd1 = equiv_dim n d01 d11 in
      let q = equiv (n+1) ~ty v0 v1 in
      let tb = qd0, qd1, Some (T.B (None, q)) in
      go sys0 sys1 @@ tb :: acc

    | V.Tube.False (d00, d01) :: sys0, V.Tube.False (d10, d11) :: sys1 ->
      let qd0 = equiv_dim n d00 d10 in
      let qd1 = equiv_dim n d01 d11 in
      let tb = qd0, qd1, None in
      go sys0 sys1 @@ tb :: acc

    | _ -> failwith "quote_sys"
  in
  go sys0 sys1 []

let rec approx_ty n ty0 ty1 =
  match V.out ty0, V.out ty1 with
  | V.Univ l0, V.Univ l1 ->
    if Lvl.greater l0 l1 then
      failwith "approx_ty: universe level too big"
    else
      ()


  | V.Pi (dom0, cod0), V.Pi (dom1, cod1) ->
    let vdom0 = V.eval_clo dom0 in
    let vdom1 = V.eval_clo dom1 in
    approx_ty n vdom1 vdom0;
    let vgen0 = V.generic vdom0 n in
    let vgen1 = V.generic vdom1 n in
    let vcod0 = V.inst_bclo cod0 vgen0 in
    let vcod1 = V.inst_bclo cod1 vgen1 in
    approx_ty (n+1) vcod0 vcod1

  | V.Sg (dom0, cod0), V.Sg (dom1, cod1) ->
    let vdom0 = V.eval_clo dom0 in
    let vdom1 = V.eval_clo dom1 in
    approx_ty n vdom0 vdom1;
    let vgen0 = V.generic vdom0 n in
    let vgen1 = V.generic vdom1 n in
    let vcod0 = V.inst_bclo cod0 vgen0 in
    let vcod1 = V.inst_bclo cod1 vgen1 in
    approx_ty (n+1) vcod0 vcod1

  | V.Ext (cod0, sys0), V.Ext (cod1, sys1) ->
    let interval = V.into V.Interval in
    let vgen = V.generic interval n in
    let dimx = V.project_dimval vgen in
    let vcod0 = V.inst_bclo cod0 vgen in
    let vcod1 = V.inst_bclo cod1 vgen in
    approx_ty (n+1) vcod0 vcod1;
    let vsys0 = V.inst_sclo sys0 dimx in
    let vsys1 = V.inst_sclo sys1 dimx in
    ignore @@ equiv_sys (n+1) ~ty:vcod0 vsys0 vsys1

  | V.Bool, V.Bool ->
    ()

  | V.Interval, V.Interval ->
    ()

  | V.Up (_, neu0), V.Up (_, neu1) ->
    ignore @@ equiv_neu n neu0 neu1

  | _ ->
    failwith "approx_ty"

let quote n ~ty el =
  equiv n ~ty el el

let quote_neu n neu =
  equiv_neu n neu neu

let quote_ty n ty =
  equiv_ty n ty ty

type variance = Covar | Iso

let rec approx_can_ ~vr ~n ~ty ~can0 ~can1 =
  match Val.out ty, Val.out can0, Val.out can1 with
  | Val.Univ lvl, Val.Pi (dom0, cod0), Val.Pi (dom1, cod1) ->
    let vdom0 = Val.eval_clo dom0 in
    let vdom1 = Val.eval_clo dom1 in
    let vgen0 = Val.generic vdom0 n in
    let vgen1 = Val.generic vdom1 n in
    let vcod0 = Val.inst_bclo cod0 vgen0 in
    let vcod1 = Val.inst_bclo cod1 vgen1 in
    let qdom = approx_can_ ~vr:Iso ~n ~ty ~can0:vdom1 ~can1:vdom0 in
    let qcod = approx_can_ ~vr ~n:(n + 1) ~ty ~can0:vcod0 ~can1:vcod1 in
    Tm.into @@ Tm.Pi (qdom, Tm.B (None, qcod))

  | Val.Univ lvl, Val.Sg (dom0, cod0), Val.Sg (dom1, cod1) ->
    let dom1, cod1 = Val.out_sg can1 in
    let vdom0 = Val.eval_clo dom0 in
    let vdom1 = Val.eval_clo dom1 in
    let vgen0 = Val.generic vdom0 n in
    let vgen1 = Val.generic vdom1 n in
    let vcod0 = Val.inst_bclo cod0 vgen0 in
    let vcod1 = Val.inst_bclo cod1 vgen1 in
    let qdom = approx_can_ ~vr:Iso ~n ~ty ~can0:vdom1 ~can1:vdom0 in
    let qcod = approx_can_ ~vr ~n:(n + 1) ~ty ~can0:vcod0 ~can1:vcod1 in
    Tm.into @@ Tm.Pi (qdom, Tm.B (None, qcod))

  | Val.Univ lvl, Val.Ext (cod0, sys0), Val.Ext (cod1, sys1) ->
    let interval = Val.into Val.Interval in
    let vgen = Val.generic interval n in
    let vcod0 = Val.inst_bclo cod0 vgen in
    let vcod1 = Val.inst_bclo cod0 vgen in
    let n' = n + 1 in
    let qcod = approx_can_ ~vr ~n:n' ~ty ~can0:vcod0 ~can1:vcod1 in
    let sys0x = Val.inst_sclo sys0 @@ Val.project_dimval vgen in
    let sys1x = Val.inst_sclo sys1 @@ Val.project_dimval vgen in
    let qsys = approx_sys ~vr ~n:n' ~ty:vcod0 ~sys0:sys0x ~sys1:sys1x in
    Tm.into @@ Tm.Ext (Tm.B (None, (qcod, qsys)))

  | Val.Univ _, Val.Interval, Val.Interval ->
    Tm.into Tm.Interval

  | Val.Univ _, Val.Bool, Val.Bool ->
    Tm.into Tm.Bool

  | Val.Univ _, Val.Univ lvl0, Val.Univ lvl1 ->
    begin
      match vr with
      | Iso ->
        if lvl0 = lvl1 then
          Tm.into @@ Tm.Univ lvl0
        else
          failwith "approx/iso: univ levels"
      | Covar ->
        if Lvl.greater lvl0 lvl1 then
          failwith @@ "approx/covar: " ^ Lvl.to_string lvl1 ^ " > " ^ Lvl.to_string lvl0
        else
          Tm.into @@ Tm.Univ lvl0
    end

  | Val.Pi (dom, cod), _, _ ->
    let vdom = Val.eval_clo dom in
    let vgen = Val.generic vdom n in
    let vcod = Val.inst_bclo cod vgen in
    let vapp0 = Val.apply can0 vgen in
    let vapp1 = Val.apply can1 vgen in
    let qbdy = approx_can_ ~vr ~n:(n+1) ~ty:vcod ~can0:vapp0 ~can1:vapp1 in
    Tm.into @@ Tm.Lam (Tm.B (None, qbdy))

  | Val.Ext (cod, sys), _, _ ->
    let interval = Val.into Val.Interval in
    let vgen = Val.generic interval n in
    let vdim = Val.project_dimval vgen in
    let vcod = Val.inst_bclo cod vgen in
    let vapp0 = Val.ext_apply can0 vdim in
    let vapp1 = Val.ext_apply can1 vdim in
    let qbdy = approx_can_ ~vr ~n:(n+1) ~ty:vcod ~can0:vapp0 ~can1:vapp1 in
    Tm.into @@ Tm.Lam (Tm.B (None, qbdy))

  | Val.Sg (dom, cod), _, _->
    let vdom = Val.eval_clo dom in
    let vcar0 = Val.car can0 in
    let vcar1 = Val.car can1 in
    let vcdr0 = Val.cdr can0 in
    let vcdr1 = Val.cdr can1 in
    let vcod = Val.inst_bclo cod vcar0 in
    let qcar = approx_can_ ~vr ~n ~ty:vdom ~can0:vcar0 ~can1:vcar1 in
    let qcdr = approx_can_ ~vr ~n ~ty:vcod ~can0:vcdr0 ~can1:vcdr1 in
    Tm.into @@ Tm.Cons (qcar, qcdr)

  | Val.Bool, Val.Tt, Val.Tt ->
    Tm.into Tm.Tt

  | Val.Bool, Val.Ff, Val.Ff ->
    Tm.into Tm.Ff

  | _, Val.Coe coe0, Val.Coe coe1 ->
    let interval = Val.into Val.Interval in
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    let qdim0 = approx_can_ ~vr ~n ~ty:interval ~can0:(Val.embed_dimval coe0.dim0) ~can1:(Val.embed_dimval coe0.dim0) in
    let qdim1 = approx_can_ ~vr ~n ~ty:interval ~can0:(Val.embed_dimval coe0.dim1) ~can1:(Val.embed_dimval coe0.dim1) in
    let vgen = Val.generic interval n in
    let vty0 = Val.inst_bclo coe0.ty vgen in
    let vty1 = Val.inst_bclo coe1.ty vgen in
    let qty = approx_can_ ~vr ~n:(n + 1) ~ty:univ ~can0:vty0 ~can1:vty1 in
    let qtm = approx_can_ ~vr ~n ~ty:(Val.inst_bclo coe0.ty @@ Val.embed_dimval coe0.dim0) ~can0:coe0.tm ~can1:coe1.tm in
    let tcoe = Tm.into @@ Tm.Coe {dim0 = qdim0; dim1 = qdim1; ty = Tm.B (None, qty); tm = qtm} in
    Tm.into @@ Tm.Up tcoe

  | _, Val.HCom hcom0, Val.HCom hcom1 ->
    let interval = Val.into Val.Interval in
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    let qdim0 = approx_can_ ~vr ~n ~ty:interval ~can0:(Val.embed_dimval hcom0.dim0) ~can1:(Val.embed_dimval hcom1.dim0) in
    let qdim1 = approx_can_ ~vr ~n ~ty:interval ~can0:(Val.embed_dimval hcom0.dim1) ~can1:(Val.embed_dimval hcom1.dim1) in
    let vty0 = hcom0.ty in
    let vty1 = hcom1.ty in
    let qty = approx_can_ ~vr ~n ~ty:univ ~can0:vty0 ~can1:vty1 in
    let qcap = approx_can_ ~vr ~n ~ty:vty0 ~can0:hcom0.cap ~can1:hcom1.cap in
    let qsys = approx_bsys ~vr ~n ~ty ~sys0:hcom0.sys ~sys1:hcom1.sys in
    let thcom = Tm.into @@ Tm.HCom {dim0 = qdim0; dim1 = qdim1; ty = qty; cap = qcap; sys = qsys} in
    Tm.into @@ Tm.Up thcom

  | _, Val.Up (_, neu0), Val.Up (_, neu1) ->
    let q = approx_neu_ ~vr ~n ~neu0 ~neu1 in
    Tm.into @@ Tm.Up q

  | Val.Interval, Val.Dim0, Val.Dim0 ->
    Tm.into Tm.Dim0

  | Val.Interval, Val.Dim1, Val.Dim1 ->
    Tm.into Tm.Dim0
    

  | _ -> 
    failwith @@ "approx_can_: " ^ Val.to_string can0 ^ " <= "  ^ Val.to_string can1

and approx_neu_ ~vr ~n ~neu0 ~neu1 =
  match Val.out neu0, Val.out neu1 with
  | Val.Lvl l0, Val.Lvl l1 ->
    if l0 != l1 then failwith "de bruijn level mismatch" else
      let ix = n - (l0 + 1) in
      Tm.into @@ Tm.Var ix

  | Val.FunApp (neu0, nfarg0), Val.FunApp (neu1, nfarg1) ->
    let quo = approx_neu_ ~vr ~n ~neu0 ~neu1 in
    let vdom, varg0 = Val.out_nf nfarg0 in
    let _, varg1 = Val.out_nf nfarg1 in
    let qarg = approx_can_ ~vr:Iso ~n ~ty:vdom ~can0:varg0 ~can1:varg1 in
    Tm.into @@ Tm.FunApp (quo, qarg)

  | Val.ExtApp (neu0, dim0), Val.ExtApp (neu1, dim1) ->
    let quo = approx_neu_ ~vr ~n ~neu0 ~neu1 in
    let interval = Val.into Val.Interval in
    let qarg = approx_can_ ~vr:Iso ~n ~ty:interval ~can0:(Val.embed_dimval dim0) ~can1:(Val.embed_dimval dim1) in
    Tm.into @@ Tm.ExtApp (quo, qarg)

  | Val.Car neu0, Val.Car neu1 ->
    let quo = approx_neu_ ~vr ~n ~neu0 ~neu1 in
    Tm.into @@ Tm.Car quo

  | Val.Cdr neu0, Val.Cdr neu1 ->
    let quo = approx_neu_ ~vr ~n ~neu0 ~neu1 in
    Tm.into @@ Tm.Cdr quo

  | Val.If if0, Val.If if1 ->
    let bool = Val.into Val.Bool in
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    let vgen = Val.generic bool n in
    let xmot0 = Val.inst_bclo if0.mot vgen in
    let xmot1 = Val.inst_bclo if1.mot vgen in
    let qmot = approx_can_ ~vr ~n:(n+1) ~ty:univ ~can0:xmot0 ~can1:xmot1 in
    let qscrut = approx_neu_ ~vr ~n ~neu0:if0.scrut ~neu1:if1.scrut in
    let tt = Val.into Val.Tt in
    let ff = Val.into Val.Ff in
    let tmot = Val.inst_bclo if0.mot tt in
    let fmot = Val.inst_bclo if1.mot ff in
    let tcase0 = Val.eval_clo if0.tcase in
    let tcase1 = Val.eval_clo if1.tcase in
    let qtcase = approx_can_ ~vr ~n ~ty:tmot ~can0:tcase0 ~can1:tcase1 in
    let fcase0 = Val.eval_clo if0.fcase in
    let fcase1 = Val.eval_clo if1.fcase in
    let qfcase = approx_can_ ~vr ~n ~ty:fmot ~can0:fcase0 ~can1:fcase1 in
    Tm.into @@ Tm.If {mot = Tm.B (None, qmot); scrut = qscrut; tcase = qtcase; fcase = qfcase}

  | _ -> failwith "approx_neu_"


and approx_sys ~vr ~n ~ty ~sys0 ~sys1 =
  let interval = Val.into Val.Interval in
  let rec go sys0 sys1 acc =
    match sys0, sys1 with
    | [], [] ->
      List.rev acc

    | Val.Tube.Delete :: sys0, _ ->
      go sys0 sys1 acc

    | _, Val.Tube.Delete :: sys1 ->
      go sys0 sys1 acc

    | Val.Tube.True ((d00, d01), clo0) :: sys0, Val.Tube.True ((d10, d11), clo1) :: sys1 ->
      let v0 = Val.eval_clo clo0 in
      let v1 = Val.eval_clo clo1 in
      let qd0 = approx_can_ ~vr ~n ~ty:interval ~can0:(Val.embed_dimval d00) ~can1:(Val.embed_dimval d10) in
      let qd1 = approx_can_ ~vr ~n ~ty:interval ~can0:(Val.embed_dimval d01) ~can1:(Val.embed_dimval d11) in
      let q = approx_can_ ~vr ~n ~ty ~can0:v0 ~can1:v1 in
      let tb = qd0, qd1, Some q in
      go sys0 sys1 @@ tb :: acc

    | Val.Tube.Indeterminate ((d00, d01), clo0) :: sys0, Val.Tube.Indeterminate ((d10, d11), clo1) :: sys1 ->
      let v0 = Val.eval_clo clo0 in
      let v1 = Val.eval_clo clo1 in
      let qd0 = approx_can_ ~vr ~n ~ty:interval ~can0:(Val.embed_dimval d00) ~can1:(Val.embed_dimval d10) in
      let qd1 = approx_can_ ~vr ~n ~ty:interval ~can0:(Val.embed_dimval d01) ~can1:(Val.embed_dimval d11) in
      let q = approx_can_ ~vr ~n ~ty ~can0:v0 ~can1:v1 in
      let tb = qd0, qd1, Some q in
      go sys0 sys1 @@ tb :: acc

    | Val.Tube.False (d00, d01) :: sys0, Val.Tube.False (d10, d11) :: sys ->
      let qd0 = approx_can_ ~vr ~n ~ty:interval ~can0:(Val.embed_dimval d00) ~can1:(Val.embed_dimval d10) in
      let qd1 = approx_can_ ~vr ~n ~ty:interval ~can0:(Val.embed_dimval d01) ~can1:(Val.embed_dimval d11) in
      let tb = qd0, qd1, None in
      go sys0 sys1 @@ tb :: acc

    | _ -> failwith "quote_sys"
  in
  go sys0 sys1 []

and approx_bsys ~vr ~n ~ty ~sys0 ~sys1 =
  let interval = Val.into Val.Interval in
  let rec go sys0 sys1 acc =
    match sys0, sys1 with
    | [], [] ->
      List.rev acc

    | Val.Tube.Delete :: sys0, _ ->
      go sys0 sys1 acc

    | _, Val.Tube.Delete :: sys1 ->
      go sys0 sys1 acc

    | Val.Tube.True ((d00, d01), clo0) :: sys0, Val.Tube.True ((d10, d11), clo1) :: sys1 ->
      let vgen = Val.generic interval n in
      let v0 = Val.inst_bclo clo0 vgen in
      let v1 = Val.inst_bclo clo1 vgen in
      let qd0 = approx_can_ ~vr ~n ~ty:interval ~can0:(Val.embed_dimval d00) ~can1:(Val.embed_dimval d10) in
      let qd1 = approx_can_ ~vr ~n ~ty:interval ~can0:(Val.embed_dimval d01) ~can1:(Val.embed_dimval d11) in
      let q = approx_can_ ~vr ~n:(n+1) ~ty ~can0:v0 ~can1:v1 in
      let tb = qd0, qd1, Some (Tm.B (None, q)) in
      go sys0 sys1 @@ tb :: acc

    | Val.Tube.Indeterminate ((d00, d01), clo0) :: sys0, Val.Tube.Indeterminate ((d10, d11), clo1) :: sys1 ->
      let vgen = Val.generic interval n in
      let v0 = Val.inst_bclo clo0 vgen in
      let v1 = Val.inst_bclo clo1 vgen in
      let qd0 = approx_can_ ~vr ~n ~ty:interval ~can0:(Val.embed_dimval d00) ~can1:(Val.embed_dimval d10) in
      let qd1 = approx_can_ ~vr ~n ~ty:interval ~can0:(Val.embed_dimval d01) ~can1:(Val.embed_dimval d11) in
      let q = approx_can_ ~vr ~n:(n + 1) ~ty ~can0:v0 ~can1:v1 in
      let tb = qd0, qd1, Some (Tm.B (None, q)) in
      go sys0 sys1 @@ tb :: acc

    | Val.Tube.False (d00, d01) :: sys0, Val.Tube.False (d10, d11) :: sys ->
      let qd0 = approx_can_ ~vr ~n ~ty:interval ~can0:(Val.embed_dimval d00) ~can1:(Val.embed_dimval d10) in
      let qd1 = approx_can_ ~vr ~n ~ty:interval ~can0:(Val.embed_dimval d01) ~can1:(Val.embed_dimval d11) in
      let tb = qd0, qd1, None in
      go sys0 sys1 @@ tb :: acc

    | _ -> failwith "quote_sys"
  in
  go sys0 sys1 []

let quote_can ~n ~ty ~can =
  approx_can_ ~vr:Iso ~n ~ty ~can0:can ~can1:can

let quote_neu ~n ~neu =
  approx_neu_ ~vr:Iso ~n ~neu0:neu ~neu1:neu

let approx ~n ~ty ~can0 ~can1 =
  ignore @@ approx_can_ ~vr:Covar ~n ~ty ~can0 ~can1

let equiv ~n ~ty ~can0 ~can1 =
  try 
    ignore @@ approx_can_ ~vr:Iso ~n ~ty ~can0 ~can1
  with
  | _ -> 
    failwith @@ Val.to_string can0 ^ " /= " ^ Val.to_string can1 ^ " : " ^ Val.to_string ty

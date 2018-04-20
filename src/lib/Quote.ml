type neu_quo = {tm : Tm.inf Tm.t; ty : Val.can Val.t}

module Ctx :
sig
  type t
  val len : t -> int
  val nth : t -> int -> Val.can Val.t

  val emp : t
  val ext : t -> Val.can Val.t -> t

  val rel : t -> DimRel.t
  val set_rel : DimRel.t -> t -> t
end =
struct
  type t = {tys : Val.can Val.t list; rel : DimRel.t; len : int}
  let len cx = cx.len
  let nth cx i = List.nth cx.tys i

  let emp = {tys = []; len = 0; rel = DimRel.emp}
  let ext cx ty = {tys = ty::cx.tys; len = cx.len + 1; rel = cx.rel}

  let rel cx = cx.rel
  let set_rel rl cx = {cx with rel = rl}
end

type ctx = Ctx.t

type variance = Covar | Iso

let rec approx_can_ ~vr ~ctx ~ty ~can0 ~can1 =
  match Val.out ty, Val.out can0, Val.out can1 with
  | Val.Univ lvl, Val.Pi (dom0, cod0), Val.Pi (dom1, cod1) ->
    let vdom0 = Val.eval_clo dom0 in
    let vdom1 = Val.eval_clo dom1 in
    let vgen0 = Val.generic vdom0 @@ Ctx.len ctx in
    let vgen1 = Val.generic vdom1 @@ Ctx.len ctx in
    let vcod0 = Val.inst_bclo cod0 vgen0 in
    let vcod1 = Val.inst_bclo cod1 vgen1 in
    let qdom = approx_can_ ~vr:Iso ~ctx ~ty ~can0:vdom1 ~can1:vdom0 in
    let qcod = approx_can_ ~vr ~ctx:(Ctx.ext ctx vdom0) ~ty ~can0:vcod0 ~can1:vcod1 in
    Tm.into @@ Tm.Pi (qdom, Tm.B qcod)

  | Val.Univ lvl, Val.Sg (dom0, cod0), Val.Sg (dom1, cod1) ->
    let dom1, cod1 = Val.out_sg can1 in
    let vdom0 = Val.eval_clo dom0 in
    let vdom1 = Val.eval_clo dom1 in
    let vgen0 = Val.generic vdom0 @@ Ctx.len ctx in
    let vgen1 = Val.generic vdom1 @@ Ctx.len ctx in
    let vcod0 = Val.inst_bclo cod0 vgen0 in
    let vcod1 = Val.inst_bclo cod1 vgen1 in
    let qdom = approx_can_ ~vr:Iso ~ctx ~ty ~can0:vdom1 ~can1:vdom0 in
    let qcod = approx_can_ ~vr ~ctx:(Ctx.ext ctx vdom0) ~ty ~can0:vcod0 ~can1:vcod1 in
    Tm.into @@ Tm.Pi (qdom, Tm.B qcod)

  | Val.Univ lvl, Val.Ext (cod0, sys0), Val.Ext (cod1, sys1) ->
    let interval = Val.into Val.Interval in
    let vgen = Val.generic interval @@ Ctx.len ctx in
    let vcod0 = Val.inst_bclo cod0 vgen in
    let vcod1 = Val.inst_bclo cod0 vgen in
    let ctx' = Ctx.ext ctx interval in
    let qcod = approx_can_ ~vr ~ctx:ctx' ~ty ~can0:vcod0 ~can1:vcod1 in
    let qsys = approx_sys ~vr ~ctx:ctx' ~ty:vcod0 ~sys0 ~sys1 in
    Tm.into @@ Tm.Ext (Tm.B (qcod, qsys))

  | Val.Univ _, Val.Interval, Val.Interval ->
    Tm.into Tm.Interval

  | Val.Univ _, Val.Bool, Val.Bool ->
    Tm.into Tm.Bool

  | Val.Univ lvl, Val.Univ lvl0, Val.Univ lvl1 ->
    begin
      match vr with
      | Iso ->
        if lvl0 = lvl1 then
          Tm.into @@ Tm.Univ lvl0
        else
          failwith "approx/iso: univ levels"
      | Covar ->
        if lvl0 <= lvl1 then
          Tm.into @@ Tm.Univ lvl0
        else
          failwith "approx/covar: univ levels"
    end

  | Val.Pi (dom, cod), _, _ ->
    let vdom = Val.eval_clo dom in
    let vgen = Val.generic vdom @@ Ctx.len ctx in
    let vcod = Val.inst_bclo cod vgen in
    let vapp0 = Val.apply can0 vgen in
    let vapp1 = Val.apply can1 vgen in
    let qbdy = approx_can_ ~vr ~ctx:(Ctx.ext ctx vdom) ~ty:vcod ~can0:vapp0 ~can1:vapp1 in
    Tm.into @@ Tm.Lam (Tm.B qbdy)

  | Val.Sg (dom, cod), _, _->
    let vdom = Val.eval_clo dom in
    let vcar0 = Val.car can0 in
    let vcar1 = Val.car can1 in
    let vcdr0 = Val.cdr can0 in
    let vcdr1 = Val.cdr can1 in
    let vcod = Val.inst_bclo cod vcar0 in
    let qcar = approx_can_ ~vr ~ctx ~ty:vdom ~can0:vcar0 ~can1:vcar1 in
    let qcdr = approx_can_ ~vr ~ctx ~ty:vcod ~can0:vcdr0 ~can1:vcdr1 in
    Tm.into @@ Tm.Cons (qcar, qcdr)

  | Val.Bool, Val.Tt, Val.Tt ->
    Tm.into Tm.Tt

  | Val.Bool, Val.Ff, Val.Ff ->
    Tm.into Tm.Ff

  | _, Val.Coe coe0, Val.Coe coe1 ->
    let interval = Val.into Val.Interval in
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    let qdim0 = approx_can_ ~vr ~ctx ~ty:interval ~can0:(Val.embed_dimval coe0.dim0) ~can1:(Val.embed_dimval coe0.dim0) in
    let qdim1 = approx_can_ ~vr ~ctx ~ty:interval ~can0:(Val.embed_dimval coe0.dim1) ~can1:(Val.embed_dimval coe0.dim1) in
    let vgen = Val.generic interval @@ Ctx.len ctx in
    let vty0 = Val.inst_bclo coe0.ty vgen in
    let vty1 = Val.inst_bclo coe1.ty vgen in
    let qty = approx_can_ ~vr ~ctx:(Ctx.ext ctx interval) ~ty:univ ~can0:vty0 ~can1:vty1 in
    let qtm = approx_can_ ~vr ~ctx ~ty:(Val.inst_bclo coe0.ty @@ Val.embed_dimval coe0.dim0) ~can0:coe0.tm ~can1:coe1.tm in
    let tcoe = Tm.into @@ Tm.Coe {dim0 = qdim0; dim1 = qdim1; ty = Tm.B qty; tm = qtm} in
    Tm.into @@ Tm.Up tcoe

  | _, Val.HCom hcom0, Val.HCom hcom1 ->
    let interval = Val.into Val.Interval in
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    let qdim0 = approx_can_ ~vr ~ctx ~ty:interval ~can0:(Val.embed_dimval hcom0.dim0) ~can1:(Val.embed_dimval hcom1.dim0) in
    let qdim1 = approx_can_ ~vr ~ctx ~ty:interval ~can0:(Val.embed_dimval hcom0.dim1) ~can1:(Val.embed_dimval hcom1.dim1) in
    let vty0 = hcom0.ty in
    let vty1 = hcom1.ty in
    let qty = approx_can_ ~vr ~ctx ~ty:univ ~can0:vty0 ~can1:vty1 in
    let qcap = approx_can_ ~vr ~ctx ~ty:vty0 ~can0:hcom0.cap ~can1:hcom1.cap in
    let qsys = approx_bsys ~vr ~ctx ~ty ~sys0:hcom0.sys ~sys1:hcom1.sys in
    let thcom = Tm.into @@ Tm.HCom {dim0 = qdim0; dim1 = qdim1; ty = qty; cap = qcap; sys = qsys} in
    Tm.into @@ Tm.Up thcom

  | _, Val.Up (_, neu0), Val.Up (_, neu1) ->
    let q = approx_neu_ ~vr ~ctx ~neu0 ~neu1 in
    Tm.into @@ Tm.Up q.tm

  | _ -> failwith "approx_can_"

and approx_neu_ ~vr ~ctx ~neu0 ~neu1 =
  match Val.out neu0, Val.out neu1 with
  | Val.Lvl l0, Val.Lvl l1 ->
    if l0 != l1 then failwith "de bruijn level mismatch" else
      let ix = Ctx.len ctx - (l0 + 1) in
      let th = Thin.from_ix ix in
      {tm = Tm.into @@ Tm.Var th;
       ty = Ctx.nth ctx ix}

  | Val.FunApp (neu0, varg0), Val.FunApp (neu1, varg1) ->
    let quo = approx_neu_ ~vr ~ctx ~neu0 ~neu1 in
    let dom, cod = Val.out_pi quo.ty in
    let vdom = Val.eval_clo dom in
    let vcod = Val.inst_bclo cod varg0 in
    let qarg = approx_can_ ~vr:Iso ~ctx ~ty:vdom ~can0:varg0 ~can1:varg1 in
    {tm = Tm.into @@ Tm.FunApp (quo.tm, qarg);
     ty = vcod}

  | Val.ExtApp (neu0, dim0), Val.ExtApp (neu1, dim1) ->
    let quo = approx_neu_ ~vr ~ctx ~neu0 ~neu1 in
    let cod, sys = Val.out_ext quo.ty in
    let interval = Val.into Val.Interval in
    let qarg = approx_can_ ~vr:Iso ~ctx ~ty:interval ~can0:(Val.embed_dimval dim0) ~can1:(Val.embed_dimval dim1) in
    let vcod = Val.inst_bclo cod @@ Val.embed_dimval dim0 in
    {tm = Tm.into @@ Tm.ExtApp (quo.tm, qarg);
     ty = vcod}


  | Val.Car neu0, Val.Car neu1 ->
    let quo = approx_neu_ ~vr ~ctx ~neu0 ~neu1 in
    let dom, _ = Val.out_sg quo.ty in
    let vdom = Val.eval_clo dom in
    {tm = Tm.into @@ Tm.Car quo.tm;
     ty = vdom}

  | Val.Cdr neu0, Val.Cdr neu1 ->
    let quo = approx_neu_ ~vr ~ctx ~neu0 ~neu1 in
    let dom, cod = Val.out_sg quo.ty in
    let vdom = Val.eval_clo dom in
    let vcar = Val.reflect vdom @@ Val.into @@ Val.Car neu0 in
    let vcod = Val.inst_bclo cod vcar in
    {tm = Tm.into @@ Tm.Cdr quo.tm;
     ty = vcod}

  | Val.If if0, Val.If if1 ->
    let bool = Val.into Val.Bool in
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    let vgen = Val.generic bool @@ Ctx.len ctx in
    let xmot0 = Val.inst_bclo if0.mot vgen in
    let xmot1 = Val.inst_bclo if1.mot vgen in
    let qmot = approx_can_ ~vr ~ctx:(Ctx.ext ctx bool) ~ty:univ ~can0:xmot0 ~can1:xmot1 in
    let qscrut = approx_neu_ ~vr ~ctx ~neu0:if0.scrut ~neu1:if1.scrut in
    let tt = Val.into Val.Tt in
    let ff = Val.into Val.Ff in
    let tmot = Val.inst_bclo if0.mot tt in
    let fmot = Val.inst_bclo if1.mot ff in
    let tcase0 = Val.eval_clo if0.tcase in
    let tcase1 = Val.eval_clo if1.tcase in
    let qtcase = approx_can_ ~vr ~ctx ~ty:tmot ~can0:tcase0 ~can1:tcase1 in
    let fcase0 = Val.eval_clo if0.fcase in
    let fcase1 = Val.eval_clo if1.fcase in
    let qfcase = approx_can_ ~vr ~ctx ~ty:fmot ~can0:fcase0 ~can1:fcase1 in
    {tm = Tm.into @@ Tm.If {mot = Tm.B qmot; scrut = qscrut.tm; tcase = qtcase; fcase = qfcase};
     ty = Val.inst_bclo if0.mot @@ Val.reflect qscrut.ty if0.scrut}

  | _ -> failwith "approx_neu_"


and approx_sys ~vr ~ctx ~ty ~sys0 ~sys1 = failwith "TODO"
(* let interval = Val.into Val.Interval in
   let rec go sys0 sys1 acc =
   match vr, sys0, sys1 with
   | _, [], [] ->
    List.rev acc

   | _, tube0 :: sys0, tube1 :: sys1 ->
    let (vd00, vd01, oclo0) = tube0 in
    let (vd10, vd11, oclo1) = tube1 in
    let qd0 = approx_can_ ~vr ~ctx ~ty:interval ~can0:(Val.embed_dimval vd00) ~can1:(Val.embed_dimval vd10) in
    let qd1 = approx_can_ ~vr ~ctx ~ty:interval ~can0:(Val.embed_dimval vd01) ~can1:(Val.embed_dimval vd11) in
    let oqv =
      match oclo0, oclo1 with
      | Some clo0, Some clo1 ->
        let v0 = Val.eval_clo clo0 in
        let v1 = Val.eval_clo clo1 in
        let qv = approx_can_ ~vr ~ctx ~ty ~can0:v0 ~can1:v1 in
        Some qv

      | None, None ->
        None

      | _ ->
        failwith "Expected Some"
    in
    go sys0 sys1 @@ (qd0, qd1, oqv) :: acc

   | _ -> failwith "approx_sys"

   in go sys0 sys1 [] *)

and approx_bsys ~vr ~ctx ~ty ~sys0 ~sys1 = failwith "TODO"
(* let interval = Val.into Val.Interval in
   let rec go sys0 sys1 acc =
   match vr, sys0, sys1 with
   | _, [], [] ->
    List.rev acc

   | _, tube0 :: sys0, tube1 :: sys1 ->
    let (vd00, vd01, obclo0) = tube0 in
    let (vd10, vd11, obclo1) = tube1 in
    let qd0 = approx_can_ ~vr ~ctx ~ty:interval ~can0:(Val.embed_dimval vd00) ~can1:(Val.embed_dimval vd10) in
    let qd1 = approx_can_ ~vr ~ctx ~ty:interval ~can0:(Val.embed_dimval vd01) ~can1:(Val.embed_dimval vd11) in
    let oqbnd =
      match obclo0, obclo1 with
      | Some bclo0, Some bclo1 ->
        let vgen = Val.generic interval @@ Ctx.len ctx in
        let v0 = Val.inst_bclo bclo0 vgen in
        let v1 = Val.inst_bclo bclo1 vgen in
        let qbnd = approx_can_ ~vr ~ctx:(Ctx.ext ctx interval) ~ty ~can0:v0 ~can1:v1 in
        Some (Tm.B qbnd)

      | None, None ->
        None

      | _ ->
        failwith "Expected Some"
    in
    go sys0 sys1 @@ (qd0, qd1, oqbnd) :: acc

   | _ -> failwith "approx_bsys"

   in go sys0 sys1 [] *)

let quote_can ~ctx ~ty ~can =
  approx_can_ ~vr:Iso ~ctx ~ty ~can0:can ~can1:can

let quote_neu ~ctx ~neu =
  approx_neu_ ~vr:Iso ~ctx ~neu0:neu ~neu1:neu

let approx ~ctx ~ty ~can0 ~can1 =
  ignore @@ approx_can_ ~vr:Covar ~ctx ~ty ~can0 ~can1

let equiv ~ctx ~ty ~can0 ~can1 =
  ignore @@ approx_can_ ~vr:Iso ~ctx ~ty ~can0 ~can1

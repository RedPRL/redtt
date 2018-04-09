type neu_quo = {tm : Tm.inf Tm.t; ty : Val.can Val.t}

module Ctx :
sig
  type t
  val len : t -> int
  val nth : t -> int -> Val.can Val.t
  val ext : t -> Val.can Val.t -> t
end =
struct
  type t = {tys : Val.can Val.t list; len : int}
  let len cx = cx.len
  let nth cx i = List.nth cx.tys i
  let ext cx ty = {tys = ty::cx.tys; len = cx.len + 1}
end

type ctx = Ctx.t

type variance = Covar | Iso

let rec approx_can_ ~vr ~ctx ~ty ~can0 ~can1 = 
  match Val.out ty, Val.out can0, Val.out can1 with
  | Val.Univ lvl, Val.Pi (dom0, cod0), _ ->
    let dom1, cod1 = Val.out_pi can1 in
    let vdom0 = Val.eval_clo dom0 in
    let vdom1 = Val.eval_clo dom1 in
    let vgen0 = Val.reflect vdom0 @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
    let vgen1 = Val.reflect vdom0 @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
    let vcod0 = Val.inst_bclo cod0 vgen0 in
    let vcod1 = Val.inst_bclo cod1 vgen1 in
    let qdom = approx_can_ ~vr:Iso ~ctx ~ty ~can0:vdom1 ~can1:vdom0 in
    let qcod = approx_can_ ~vr ~ctx:(Ctx.ext ctx vdom0) ~ty ~can0:vcod0 ~can1:vcod1 in
    Tm.into @@ Tm.Pi (qdom, Tm.B qcod)

  | Val.Univ lvl, _, Val.Pi (dom1, cod1) ->
    let dom0, cod0 = Val.out_pi can0 in
    let vdom0 = Val.eval_clo dom0 in
    let vdom1 = Val.eval_clo dom1 in
    let vgen0 = Val.reflect vdom0 @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
    let vgen1 = Val.reflect vdom0 @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
    let vcod0 = Val.inst_bclo cod0 vgen0 in
    let vcod1 = Val.inst_bclo cod1 vgen1 in
    let qdom = approx_can_ ~vr:Iso ~ctx ~ty ~can0:vdom1 ~can1:vdom0 in
    let qcod = approx_can_ ~vr ~ctx:(Ctx.ext ctx vdom0) ~ty ~can0:vcod0 ~can1:vcod1 in
    Tm.into @@ Tm.Pi (qdom, Tm.B qcod)

  | Val.Univ lvl, Val.Sg (dom0, cod0), _ ->
    let dom1, cod1 = Val.out_sg can1 in
    let vdom0 = Val.eval_clo dom0 in
    let vdom1 = Val.eval_clo dom1 in
    let vgen0 = Val.reflect vdom0 @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
    let vgen1 = Val.reflect vdom0 @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
    let vcod0 = Val.inst_bclo cod0 vgen0 in
    let vcod1 = Val.inst_bclo cod1 vgen1 in
    let qdom = approx_can_ ~vr:Iso ~ctx ~ty ~can0:vdom1 ~can1:vdom0 in
    let qcod = approx_can_ ~vr ~ctx:(Ctx.ext ctx vdom0) ~ty ~can0:vcod0 ~can1:vcod1 in
    Tm.into @@ Tm.Pi (qdom, Tm.B qcod)

  | Val.Univ lvl, _, Val.Sg (dom1, cod1) ->
    let dom0, cod0 = Val.out_sg can0 in
    let vdom0 = Val.eval_clo dom0 in
    let vdom1 = Val.eval_clo dom1 in
    let vgen0 = Val.reflect vdom0 @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
    let vgen1 = Val.reflect vdom0 @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
    let vcod0 = Val.inst_bclo cod0 vgen0 in
    let vcod1 = Val.inst_bclo cod1 vgen1 in
    let qdom = approx_can_ ~vr:Iso ~ctx ~ty ~can0:vdom1 ~can1:vdom0 in
    let qcod = approx_can_ ~vr ~ctx:(Ctx.ext ctx vdom0) ~ty ~can0:vcod0 ~can1:vcod1 in
    Tm.into @@ Tm.Sg (qdom, Tm.B qcod)

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

  | Val.Univ lvl, Val.Ext (tag0, ty0, sys0), Val.Ext (tag1, ty1, sys1) ->
    if tag0 != tag1 then failwith "tag mismatch" else
      let qty = approx_can_ ~vr ~ctx ~ty ~can0:ty0 ~can1:ty1 in
      begin
        match approx_sys ~vr ~tag:tag0 ~ctx ~ty ~sys0 ~sys1 with
        | qsys -> Tm.into @@ Tm.Ext (tag0, qty, qsys)
        | exception exn ->
          match vr with
          | Covar -> approx_can_ ~vr ~ctx ~ty ~can0:ty0 ~can1
          | Iso -> raise exn
      end

  | Val.Univ lvl, Val.Ext (tag0, ty0, sys0), _ ->
    begin
      match vr with
      | Covar -> approx_can_ ~vr ~ctx ~ty ~can0:ty0 ~can1
      | _ -> failwith "approx_can_/univ/ext"
    end

  | Val.Pi (dom, cod), _, _ ->
    let vdom = Val.eval_clo dom in
    let vgen = Val.reflect vdom @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
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

  | _, Val.Coe coe0, Val.Coe coe1 ->
    let coe0' = reduce_coe ~ctx ~tag:coe0.tag ~ty ~dim0:coe0.dim0 ~dim1:coe0.dim1 ~bty:coe0.ty ~tm:coe0.tm in
    let coe1' = reduce_coe ~ctx ~tag:coe1.tag ~ty ~dim0:coe1.dim0 ~dim1:coe1.dim1 ~bty:coe1.ty ~tm:coe1.tm in
    approx_coe_contracta ~vr ~ctx ~ty ~can0:coe0' ~can1:coe1'

  | _, Val.Coe coe0, _ ->
    let coe0' = reduce_coe ~ctx ~tag:coe0.tag ~ty ~dim0:coe0.dim0 ~dim1:coe0.dim1 ~bty:coe0.ty ~tm:coe0.tm in
    approx_coe_contracta ~vr ~ctx ~ty ~can0:coe0' ~can1

  | _, _, Val.Coe coe1 ->
    let coe1' = reduce_coe ~ctx ~tag:coe1.tag ~ty ~dim0:coe1.dim0 ~dim1:coe1.dim1 ~bty:coe1.ty ~tm:coe1.tm in
    approx_coe_contracta ~vr ~ctx ~ty ~can0 ~can1:coe1'

  | _, Val.HCom hcom0, Val.HCom hcom1 ->
    let hcom0' = reduce_hcom ~ctx ~dim0:hcom0.dim0 ~dim1:hcom0.dim1 ~ty:hcom0.ty ~cap:hcom0.cap ~sys:hcom0.sys in
    let hcom1' = reduce_hcom ~ctx ~dim0:hcom1.dim0 ~dim1:hcom1.dim1 ~ty:hcom1.ty ~cap:hcom1.cap ~sys:hcom1.sys in
    approx_hcom_contracta ~vr ~ctx ~ty ~can0:hcom0' ~can1:hcom1'

  | _, Val.HCom hcom0, _ ->
    let hcom0' = reduce_hcom ~ctx ~dim0:hcom0.dim0 ~dim1:hcom0.dim1 ~ty:hcom0.ty ~cap:hcom0.cap ~sys:hcom0.sys in
    approx_hcom_contracta ~vr ~ctx ~ty ~can0:hcom0' ~can1

  | _, _, Val.HCom hcom1 ->
    let hcom1' = reduce_hcom ~ctx ~dim0:hcom1.dim0 ~dim1:hcom1.dim1 ~ty:hcom1.ty ~cap:hcom1.cap ~sys:hcom1.sys in
    approx_hcom_contracta ~vr ~ctx ~ty ~can0 ~can1:hcom1'

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

  | Val.App (neu0, varg0), Val.App (neu1, varg1) ->
    let quo = approx_neu_ ~vr ~ctx ~neu0 ~neu1 in
    let dom, cod = Val.out_pi quo.ty in
    let vdom = Val.eval_clo dom in
    let vcod = Val.inst_bclo cod varg0 in
    let qarg = approx_can_ ~vr:Iso ~ctx ~ty:vdom ~can0:varg0 ~can1:varg1 in
    {tm = Tm.into @@ Tm.App (quo.tm, qarg);
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

  | _ -> failwith "approx_neu_"


and approx_sys ~vr ~tag ~ctx ~ty ~sys0 ~sys1 =
  let interval = Val.into @@ Val.Interval tag in
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

  in go sys0 sys1 []

and approx_bsys ~vr ~tag ~ctx ~ty ~sys0 ~sys1 =
  let interval = Val.into @@ Val.Interval tag in
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
          let vgen = Val.reflect interval @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
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

  in go sys0 sys1 []

and approx_coe_contracta ~vr ~ctx ~ty ~can0 ~can1 =
  match Val.out can0, Val.out can1 with
  | Val.Coe coe0, Val.Coe coe1 ->
    if coe0.tag != coe1.tag then failwith "tag mismatch" else
      let interval = Val.into @@ Val.Interval coe0.tag in
      let univ = Val.into @@ Val.Univ Lvl.Omega in
      let qdim0 = approx_can_ ~vr ~ctx ~ty:interval ~can0:coe0.dim0 ~can1:coe0.dim0 in
      let qdim1 = approx_can_ ~vr ~ctx ~ty:interval ~can0:coe0.dim1 ~can1:coe0.dim1 in
      let vgen = Val.reflect interval @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
      let vty0 = Val.inst_bclo coe0.ty vgen in
      let vty1 = Val.inst_bclo coe1.ty vgen in
      let qty = approx_can_ ~vr ~ctx:(Ctx.ext ctx interval) ~ty:univ ~can0:vty0 ~can1:vty1 in
      let qtm = approx_can_ ~vr ~ctx ~ty:(Val.inst_bclo coe0.ty coe0.dim0) ~can0:coe0.tm ~can1:coe1.tm in
      let tcoe = Tm.into @@ Tm.Coe {tag = coe0.tag; dim0 = qdim0; dim1 = qdim1; ty = Tm.B qty; tm = qtm} in
      Tm.into @@ Tm.Up tcoe

  | _, _ ->
    approx_can_ ~vr ~ctx ~ty ~can0 ~can1

and approx_hcom_contracta ~vr ~ctx ~ty ~can0 ~can1 =
  match Val.out can0, Val.out can1 with
  | Val.HCom hcom0, Val.HCom hcom1 ->
    if hcom0.tag != hcom1.tag then failwith "tag mismatch" else
      let interval = Val.into @@ Val.Interval hcom0.tag in
      let univ = Val.into @@ Val.Univ Lvl.Omega in
      let qdim0 = approx_can_ ~vr ~ctx ~ty:interval ~can0:hcom0.dim0 ~can1:hcom1.dim0 in
      let qdim1 = approx_can_ ~vr ~ctx ~ty:interval ~can0:hcom0.dim1 ~can1:hcom1.dim1 in
      let vty0 = Val.eval_clo hcom0.ty in
      let vty1 = Val.eval_clo hcom1.ty in
      let qty = approx_can_ ~vr ~ctx ~ty:univ ~can0:vty0 ~can1:vty1 in
      let qcap = approx_can_ ~vr ~ctx ~ty:vty0 ~can0:hcom0.cap ~can1:hcom1.cap in
      let qsys = approx_bsys ~vr ~tag:hcom0.tag ~ctx ~ty ~sys0:hcom0.sys ~sys1:hcom1.sys in
      let thcom = Tm.into @@ Tm.HCom {tag = hcom0.tag; dim0 = qdim0; dim1 = qdim1; ty = qty; cap = qcap; sys = qsys} in
      Tm.into @@ Tm.Up thcom

  | _, _ ->
    approx_can_ ~vr ~ctx ~ty ~can0 ~can1


(* Invariant: this should only be called on neutral and base types.
   Invariant: ty = bty[dim1] *)
and reduce_coe ~ctx ~tag ~ty ~dim0 ~dim1 ~bty ~tm =
  let vd0 = Val.project_dimval dim0 in
  let vd1 = Val.project_dimval dim1 in
  match DimVal.compare vd0 vd1 with
  | DimVal.Same ->
    tm

  | _ ->
    match tag with
    | Cube.Equality ->
      let vty0 = Val.inst_bclo bty dim0 in
      let univ = Val.into @@ Val.Univ Lvl.Omega in
      begin
        match approx_can_ ~vr:Iso ~ctx ~ty:univ ~can0:vty0 ~can1:ty with
        | _ -> tm
        | exception _ ->
          reduce_rigid_coe ~ctx ~ty ~tag ~dim0 ~dim1 ~bty ~tm
      end

    | Cube.Path ->
      reduce_rigid_coe ~ctx ~ty ~tag ~dim0 ~dim1 ~bty ~tm

and reduce_rigid_coe ~ctx ~ty ~tag ~dim0 ~dim1 ~bty ~tm =
  let interval = Val.into @@ Val.Interval tag in
  let vgen = Val.reflect interval @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
  match Val.out @@ Val.inst_bclo bty vgen with
  | Val.Up (univ, tyneu) ->
    Val.into @@ Val.Coe {tag; dim0; dim1; ty = bty; tm}

  | Val.Univ _ ->
    tm

  | _ -> failwith "quote_coe: missing case (?)"



(* Invariant: this should only be called on neutral and base types. *)
and reduce_hcom ~ctx ~dim0 ~dim1 ~ty ~cap ~sys =
  let vd0 = Val.project_dimval dim0 in 
  let vd1 = Val.project_dimval dim1 in
  match DimVal.compare vd0 vd1 with
  | DimVal.Same ->
    cap
  | _ ->
    reduce_rigid_hcom ~ctx ~dim0 ~dim1 ~ty ~cap ~sys


and reduce_rigid_hcom ~ctx ~dim0 ~dim1 ~ty ~cap ~sys =
  let interval = Val.into @@ Val.Interval Cube.Path in
  let rec go tubes =
    match tubes with
    | [] ->
      Val.into @@ Val.HCom {tag = Cube.Path; dim0; dim1; ty; cap; sys}

    | (dim0', dim1', obclo) :: tubes ->
      match DimVal.compare dim0' dim1', obclo with
      | DimVal.Same, Some bclo ->
        Val.inst_bclo bclo (Val.embed_dimval dim1')

      | _ ->
        match approx_can_ ~vr:Iso ~ctx ~ty:interval ~can0:(Val.embed_dimval dim0') ~can1:(Val.embed_dimval dim1') with
        | exception _ ->
          go tubes
        | _ ->
          match obclo with
          | Some bclo ->
            Val.inst_bclo bclo (Val.embed_dimval dim1')
          | None ->
            failwith "reduce_path_hcom: expected Some"
  in
  go sys



let quote_can ~ctx ~ty ~can = 
  approx_can_ ~vr:Iso ~ctx ~ty ~can0:can ~can1:can

let quote_neu ~ctx ~neu = 
  approx_neu_ ~vr:Iso ~ctx ~neu0:neu ~neu1:neu

let approx ~ctx ~ty ~can0 ~can1 =
  ignore @@ approx_can_ ~vr:Covar ~ctx ~ty ~can0 ~can1

let equiv ~ctx ~ty ~can0 ~can1 =
  ignore @@ approx_can_ ~vr:Iso ~ctx ~ty ~can0 ~can1

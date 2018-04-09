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

let rec approx_can ~vr ~ctx ~ty ~can0 ~can1 = 
  match Val.out ty, Val.out can0, Val.out can1 with
  | Val.Univ lvl, Val.Pi (dom0, cod0), _ ->
    let dom1, cod1 = Val.out_pi can1 in
    let vdom0 = Val.eval_clo dom0 in
    let vdom1 = Val.eval_clo dom1 in
    let vgen0 = Val.reflect vdom0 @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
    let vgen1 = Val.reflect vdom0 @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
    let vcod0 = Val.inst_bclo cod0 vgen0 in
    let vcod1 = Val.inst_bclo cod1 vgen1 in
    let qdom = approx_can ~vr:Iso ~ctx ~ty ~can0:vdom1 ~can1:vdom0 in
    let qcod = approx_can ~vr ~ctx:(Ctx.ext ctx vdom0) ~ty ~can0:vcod0 ~can1:vcod1 in
    Tm.into @@ Tm.Pi (qdom, Tm.B qcod)

  | Val.Univ lvl, _, Val.Pi (dom1, cod1) ->
    let dom0, cod0 = Val.out_pi can0 in
    let vdom0 = Val.eval_clo dom0 in
    let vdom1 = Val.eval_clo dom1 in
    let vgen0 = Val.reflect vdom0 @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
    let vgen1 = Val.reflect vdom0 @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
    let vcod0 = Val.inst_bclo cod0 vgen0 in
    let vcod1 = Val.inst_bclo cod1 vgen1 in
    let qdom = approx_can ~vr:Iso ~ctx ~ty ~can0:vdom1 ~can1:vdom0 in
    let qcod = approx_can ~vr ~ctx:(Ctx.ext ctx vdom0) ~ty ~can0:vcod0 ~can1:vcod1 in
    Tm.into @@ Tm.Pi (qdom, Tm.B qcod)

  | Val.Univ lvl, Val.Sg (dom0, cod0), _ ->
    let dom1, cod1 = Val.out_sg can1 in
    let vdom0 = Val.eval_clo dom0 in
    let vdom1 = Val.eval_clo dom1 in
    let vgen0 = Val.reflect vdom0 @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
    let vgen1 = Val.reflect vdom0 @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
    let vcod0 = Val.inst_bclo cod0 vgen0 in
    let vcod1 = Val.inst_bclo cod1 vgen1 in
    let qdom = approx_can ~vr:Iso ~ctx ~ty ~can0:vdom1 ~can1:vdom0 in
    let qcod = approx_can ~vr ~ctx:(Ctx.ext ctx vdom0) ~ty ~can0:vcod0 ~can1:vcod1 in
    Tm.into @@ Tm.Pi (qdom, Tm.B qcod)

  | Val.Univ lvl, _, Val.Sg (dom1, cod1) ->
    let dom0, cod0 = Val.out_sg can0 in
    let vdom0 = Val.eval_clo dom0 in
    let vdom1 = Val.eval_clo dom1 in
    let vgen0 = Val.reflect vdom0 @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
    let vgen1 = Val.reflect vdom0 @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
    let vcod0 = Val.inst_bclo cod0 vgen0 in
    let vcod1 = Val.inst_bclo cod1 vgen1 in
    let qdom = approx_can ~vr:Iso ~ctx ~ty ~can0:vdom1 ~can1:vdom0 in
    let qcod = approx_can ~vr ~ctx:(Ctx.ext ctx vdom0) ~ty ~can0:vcod0 ~can1:vcod1 in
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
      let qty = approx_can ~vr ~ctx ~ty ~can0:ty0 ~can1:ty1 in
      begin
        match approx_sys ~vr ~tag:tag0 ~ctx ~ty ~sys0 ~sys1 with
        | qsys -> Tm.into @@ Tm.Ext (tag0, qty, qsys)
        | exception exn ->
          match vr with
          | Covar -> approx_can ~vr ~ctx ~ty ~can0:ty0 ~can1
          | Iso -> raise exn
      end

  | Val.Univ lvl, Val.Ext (tag0, ty0, sys0), _ ->
    begin
      match vr with
      | Covar -> approx_can ~vr ~ctx ~ty ~can0:ty0 ~can1
      | _ -> failwith "approx_can/univ/ext"
    end

  | Val.Pi (dom, cod), _, _ ->
    let vdom = Val.eval_clo dom in
    let vgen = Val.reflect vdom @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
    let vcod = Val.inst_bclo cod vgen in
    let vapp0 = Val.apply can0 vgen in
    let vapp1 = Val.apply can1 vgen in
    let qbdy = approx_can ~vr ~ctx:(Ctx.ext ctx vdom) ~ty:vcod ~can0:vapp0 ~can1:vapp1 in
    Tm.into @@ Tm.Lam (Tm.B qbdy)

  | Val.Sg (dom, cod), _, _->
    let vdom = Val.eval_clo dom in
    let vcar0 = Val.car can0 in
    let vcar1 = Val.car can1 in
    let vcdr0 = Val.cdr can0 in
    let vcdr1 = Val.cdr can1 in
    let vcod = Val.inst_bclo cod vcar0 in
    let qcar = approx_can ~vr ~ctx ~ty:vdom ~can0:vcar0 ~can1:vcar1 in
    let qcdr = approx_can ~vr ~ctx ~ty:vcod ~can0:vcdr0 ~can1:vcdr1 in
    Tm.into @@ Tm.Cons (qcar, qcdr)


  | _ -> failwith "approx_can"


and approx_sys ~vr ~tag ~ctx ~ty ~sys0 ~sys1 =
  let interval = Val.into @@ Val.Interval tag in
  let rec go sys0 sys1 acc =   
    match vr, sys0, sys1 with
    | _, [], [] ->
      List.rev acc

    | _, tube0 :: sys0, tube1 :: sys1 ->
      let (vd00, vd01, oclo0) = tube0 in
      let (vd10, vd11, oclo1) = tube1 in
      let qd0 = approx_can ~vr ~ctx ~ty:interval ~can0:(Val.embed_dimval vd00) ~can1:(Val.embed_dimval vd10) in
      let qd1 = approx_can ~vr ~ctx ~ty:interval ~can0:(Val.embed_dimval vd01) ~can1:(Val.embed_dimval vd11) in
      let oqv =
        match oclo0, oclo1 with
        | Some clo0, Some clo1 ->
          let v0 = Val.eval_clo clo0 in
          let v1 = Val.eval_clo clo1 in
          let qv = approx_can ~vr ~ctx ~ty ~can0:v0 ~can1:v1 in
          Some qv

        | None, None ->
          None

        | _ ->
          failwith "foo"
      in
      go sys0 sys1 @@ (qd0, qd1, oqv) :: acc

    | _ -> failwith "approx_sys"

  in go sys0 sys1 []


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
        match approx_can ~vr:Iso ~ctx ~ty:univ ~can0:vty0 ~can1:ty with
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
and reduce_hcom ~ctx ~tag ~dim0 ~dim1 ~ty ~cap ~sys =
  match tag with 
  | Cube.Equality ->
    cap

  | Cube.Path ->
    let vd0 = Val.project_dimval dim0 in 
    let vd1 = Val.project_dimval dim1 in
    match DimVal.compare vd0 vd1 with
    | DimVal.Same ->
      cap
    | _ ->
      reduce_path_hcom ~ctx ~dim0 ~dim1 ~ty ~cap ~sys

and reduce_path_hcom ~ctx ~dim0 ~dim1 ~ty ~cap ~sys =
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
       match approx_can ~vr:Iso ~ctx ~ty:interval ~can0:(Val.embed_dimval dim0') ~can1:(Val.embed_dimval dim1') with
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











let rec quote_can ~ctx ~ty ~can =
  match Val.out ty, Val.out can with
  | Val.Univ lvl, Val.Pi (dom, cod) ->
    let vdom = Val.eval_clo dom in
    let qdom = quote_can ~ctx ~ty ~can:vdom in
    let vgen = Val.reflect vdom @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
    let vcod = Val.inst_bclo cod vgen in
    let qcod = quote_can ~ctx:(Ctx.ext ctx vdom) ~ty ~can:vcod in
    Tm.into @@ Tm.Pi (qdom, Tm.B qcod)

  | Val.Univ lvl, Val.Sg (dom, cod) ->
    let vdom = Val.eval_clo dom in
    let qdom = quote_can ~ctx ~ty ~can:vdom in
    let vgen = Val.reflect vdom @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
    let vcod = Val.inst_bclo cod vgen in
    let qcod = quote_can ~ctx:(Ctx.ext ctx vdom) ~ty ~can:vcod in
    Tm.into @@ Tm.Sg (qdom, Tm.B qcod)

  | Val.Univ lvl, Val.Interval tag ->
    Tm.into @@ Tm.Interval tag

  | Val.Pi (dom, cod), _ ->
    let vdom = Val.eval_clo dom in
    let vgen = Val.reflect vdom @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
    let vcod = Val.inst_bclo cod vgen in
    let vapp = Val.apply can vgen in
    let qbdy = quote_can ~ctx:(Ctx.ext ctx vdom) ~ty:vcod ~can:vapp in
    Tm.into @@ Tm.Lam (Tm.B qbdy)

  | Val.Sg (dom, cod), _ ->
    let vdom = Val.eval_clo dom in
    let vcar = Val.car can in
    let vcdr = Val.cdr can in
    let vcod = Val.inst_bclo cod vcar in
    let qcar = quote_can ~ctx ~ty:vdom ~can:vcar in
    let qcdr = quote_can ~ctx ~ty:vcod ~can:vcdr in
    Tm.into @@ Tm.Cons (qcar, qcdr)

  | Val.Ext (_, vdom, _), _ ->
    (* TODO: is this correct? I think that it is, because of invariants that are maintained in evaluation. *)
    quote_can ~ctx ~ty:vdom ~can

  | _, Val.Up (ty, neu) ->
    let qneu = quote_neu ~ctx ~neu in
    Tm.into @@ Tm.Up qneu.tm

  | _, Val.Coe {tag; dim0; dim1; ty = bty; tm} ->
    quote_coe ~ctx ~tag ~ty ~dim0 ~dim1 ~bty ~tm

  | _, Val.HCom {tag; dim0; dim1; cap; sys; _} ->
    quote_hcom ~ctx ~tag ~dim0 ~dim1 ~ty ~cap ~sys

  | _ -> failwith "quot_can: unhandled case"

(* Invariant: this should only be called on neutral and base types.
   Invariant: ty = bty[dim1] *)
and quote_coe ~ctx ~tag ~ty ~dim0 ~dim1 ~bty ~tm =
  let vd0 = Val.project_dimval dim0 in
  let vd1 = Val.project_dimval dim1 in
  match DimVal.compare vd0 vd1 with
  | DimVal.Same ->
    quote_can ~ctx ~ty ~can:tm

  | _ ->
    match tag with
    | Cube.Equality ->
      let vty0 = Val.inst_bclo bty dim0 in
      let univ = Val.into @@ Val.Univ Lvl.Omega in
      let qty0 = quote_can ~ctx ~ty:univ ~can:vty0 in
      let qty = quote_can ~ctx ~ty:univ ~can:ty in
      if Tm.eq qty0 qty then 
        quote_can ~ctx ~ty ~can:tm
      else 
        quote_rigid_coe ~ctx ~ty ~tag ~dim0 ~dim1 ~bty ~tm

    | Cube.Path ->
      quote_rigid_coe ~ctx ~ty ~tag ~dim0 ~dim1 ~bty ~tm

and quote_rigid_coe ~ctx ~ty ~tag ~dim0 ~dim1 ~bty ~tm =
  let interval = Val.into @@ Val.Interval tag in
  let vgen = Val.reflect interval @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
  match Val.out @@ Val.inst_bclo bty vgen with
  | Val.Up (univ, tyneu) ->
    let ty0 = Val.inst_bclo bty dim0 in
    let qtm = quote_can ~ctx ~ty:ty0 ~can:tm in
    let qdim0 = quote_can ~ctx ~ty:interval ~can:dim0 in
    let qdim1 = quote_can ~ctx ~ty:interval ~can:dim1 in
    let qty = quote_neu ~ctx:(Ctx.ext ctx interval) ~neu:tyneu in
    let tybnd = Tm.B (Tm.into @@ Tm.Up qty.tm) in
    let tcoe = Tm.into @@ Tm.Coe {tag; dim0 = qdim0; dim1 = qdim1; ty = tybnd; tm = qtm} in
    Tm.into @@ Tm.Up tcoe

  | Val.Univ _ ->
    quote_can ~ctx ~ty ~can:tm

  | _ -> failwith "quote_coe: missing case (?)"



(* Invariant: this should only be called on neutral and base types. *)
and quote_hcom ~ctx ~tag ~dim0 ~dim1 ~ty ~cap ~sys =
  match tag with 
  | Cube.Equality ->
    quote_can ~ctx ~ty ~can:cap

  | Cube.Path ->
    let vd0 = Val.project_dimval dim0 in 
    let vd1 = Val.project_dimval dim1 in
    match DimVal.compare vd0 vd1 with
    | DimVal.Same ->
      quote_can ~ctx ~ty ~can:cap
    | _ ->
      quote_path_hcom ~ctx ~dim0 ~dim1 ~ty ~cap ~sys

and quote_path_hcom ~ctx ~dim0 ~dim1 ~ty ~cap ~sys =
  let interval = Val.into @@ Val.Interval Cube.Path in
  let rec go tubes acc =
    match tubes with
    | [] ->
      let tsys = List.rev acc in
      let qdim0 = quote_can ~ctx ~ty:interval ~can:dim0 in
      let qdim1 = quote_can ~ctx ~ty:interval ~can:dim1 in
      let univ = Val.into @@ Val.Univ Lvl.Omega in
      let qty = quote_can ~ctx ~ty:univ ~can:ty in
      let qcap = quote_can ~ctx ~ty ~can:cap in
      let thcom = Tm.into @@ Tm.HCom {tag = Cube.Path; dim0 = qdim0; dim1 = qdim1; ty = qty; cap = qcap; sys = tsys} in
      Tm.into @@ Tm.Up thcom

    | (dim0', dim1', obclo) :: tubes ->
      match DimVal.compare dim0' dim1', obclo with
      | DimVal.Same, Some bclo ->
        let v = Val.inst_bclo bclo (Val.embed_dimval dim1') in
        quote_can ~ctx ~ty:ty ~can:v

      | _ ->
        let qdim0' = quote_can ~ctx ~ty:interval ~can:(Val.embed_dimval dim0') in
        let qdim1' = quote_can ~ctx ~ty:interval ~can:(Val.embed_dimval dim1') in
        let go_bclo bclo =
          let vgen = Val.reflect interval @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
          let v = Val.inst_bclo bclo vgen in
          Tm.B (quote_can ~ctx:(Ctx.ext ctx interval) ~ty:ty ~can:v)
        in
        let qbnd = Option.map go_bclo obclo in
        let qtube = (qdim0', qdim1', qbnd) in
        go tubes (qtube :: acc)
  in
  go sys []


and quote_neu ~ctx ~neu =
  match Val.out neu with 
  | Val.Lvl l ->
    let ix = Ctx.len ctx - (l + 1) in
    let th = Thin.from_ix ix in
    {tm = Tm.into @@ Tm.Var th; 
     ty = Ctx.nth ctx ix}

  | Val.App (neu, varg) ->
    let quo = quote_neu ~ctx ~neu in
    let dom, cod = Val.out_pi quo.ty in
    let vdom = Val.eval_clo dom in
    let vcod = Val.inst_bclo cod varg in
    let qarg = quote_can ~ctx ~ty:vdom ~can:varg in
    {tm = Tm.into @@ Tm.App (quo.tm, qarg);
     ty = vcod}

  | Val.Car neu ->
    let quo = quote_neu ~ctx ~neu in
    let dom, _ = Val.out_sg quo.ty in
    let vdom = Val.eval_clo dom in
    {tm = Tm.into @@ Tm.Car quo.tm;
     ty = vdom}

  | Val.Cdr neu ->
    let quo = quote_neu ~ctx ~neu in
    let dom, cod = Val.out_sg quo.ty in
    let vdom = Val.eval_clo dom in
    let vcar = Val.reflect vdom @@ Val.into @@ Val.Car neu in
    let vcod = Val.inst_bclo cod vcar in
    {tm = Tm.into @@ Tm.Cdr quo.tm;
     ty = vcod}

  | _ -> failwith "Bug in OCaml's exhaustiveness checker + gadts :("
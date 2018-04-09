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

  | Val.Ext (vdom, _), _ ->
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

and quote_coe ~ctx ~tag ~ty ~dim0 ~dim1 ~bty ~tm =
  let vd0 = Val.project_dimval dim0 in
  let vd1 = Val.project_dimval dim1 in
  match DimVal.compare vd0 vd1 with
  | DimVal.Same ->
    quote_can ~ctx ~ty ~can:tm

  | _ ->
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

and quote_hcom ~ctx ~tag ~dim0 ~dim1 ~ty ~cap ~sys =
  let vd0 = Val.project_dimval dim0 in 
  let vd1 = Val.project_dimval dim1 in
  match DimVal.compare vd0 vd1 with
  | DimVal.Same ->
    quote_can ~ctx ~ty ~can:cap

  | _ ->
    match Val.out ty with
    | Val.Up (univ, tyneu) ->
      let interval = Val.into @@ Val.Interval tag in
      let rec go tubes acc =
        match tubes with
        | [] ->
          let tsys = List.rev acc in
          let qdim0 = quote_can ~ctx ~ty:interval ~can:dim0 in
          let qdim1 = quote_can ~ctx ~ty:interval ~can:dim1 in
          let qty = quote_neu ~ctx ~neu:tyneu in
          let qcap = quote_can ~ctx ~ty ~can:cap in
          let thcom = Tm.into @@ Tm.HCom {tag; dim0 = qdim0; dim1 = qdim1; ty = Tm.into @@ Tm.Up qty.tm; cap = qcap; sys = tsys} in
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

    | _ ->
      (* In this case, 'ty' is guaranteed to be a universe or base type. *)
      match tag with
      | Cube.Equality ->
        (* Since we are in the cubical structure for equality (not paths), we can project out the cap *)
        quote_can ~ctx ~ty ~can:cap


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
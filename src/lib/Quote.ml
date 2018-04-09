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
  match Val.out ty with
  | Val.Univ lvl ->
    quote_can_ty ~ctx ~lvl ~ty:can

  | Val.Pi (dom, cod) ->
    let vdom = Val.eval_clo dom in
    let vgen = Val.reflect vdom @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
    let vcod = Val.inst_bclo cod vgen in
    let vapp = Val.apply can vgen in
    let qbdy = quote_can ~ctx:(Ctx.ext ctx vdom) ~ty:vcod ~can:vapp in
    Tm.into @@ Tm.Lam (Tm.B qbdy)

  | Val.Sg (dom, cod) ->
    let vdom = Val.eval_clo dom in
    let vcar = Val.car can in
    let vcdr = Val.cdr can in
    let vcod = Val.inst_bclo cod vcar in
    let qcar = quote_can ~ctx ~ty:vdom ~can:vcar in
    let qcdr = quote_can ~ctx ~ty:vcod ~can:vcdr in
    Tm.into @@ Tm.Cons (qcar, qcdr)

  | Val.Ext (vdom, _) ->
    (* TODO: is this correct? I think that it is, because of invariants that are maintained in evaluation. *)
    quote_can ~ctx ~ty:vdom ~can

  | _ -> failwith "TODO: quote_can"

and quote_can_ty ~ctx ~lvl ~ty = 
  match Val.out ty with
  | Val.Pi (dom, cod) ->
    let vdom = Val.eval_clo dom in
    let qdom = quote_can_ty ~ctx ~lvl ~ty:vdom in
    let vgen = Val.reflect vdom @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
    let vcod = Val.inst_bclo cod vgen in
    let qcod = quote_can_ty ~ctx:(Ctx.ext ctx vdom) ~lvl ~ty:vcod in
    Tm.into @@ Tm.Pi (qdom, Tm.B qcod)

  | Val.Sg (dom, cod) ->
    let vdom = Val.eval_clo dom in
    let qdom = quote_can_ty ~ctx ~lvl ~ty:vdom in
    let vgen = Val.reflect vdom @@ Val.into @@ Val.Lvl (Ctx.len ctx) in
    let vcod = Val.inst_bclo cod vgen in
    let qcod = quote_can_ty ~ctx:(Ctx.ext ctx vdom) ~lvl ~ty:vcod in
    Tm.into @@ Tm.Sg (qdom, Tm.B qcod)

  | _ -> failwith "TODO: quote_can_ty"

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
type mode = Rel | Irrel

module Ctx :
sig
  type t
  val emp : t
  val ext : t -> Val.can Val.t -> t
  val lookup : Thin.t -> t -> Val.can Val.t
  val len : t -> int

  val env : t -> Val.env
  val qctx : t -> Quote.ctx
end =
struct
  type t =
    {tys : Val.can Val.t list;
     env : Val.env;
     qctx : Quote.ctx;
     len : int}

  let emp =
    {tys = [];
     env = [];
     qctx = Quote.Ctx.emp;
     len = 0}

  let ext cx v =
    {tys = v :: cx.tys;
     env = Val.generic v cx.len :: cx.env;
     qctx = Quote.Ctx.ext cx.qctx v;
     len = cx.len + 1}

  let lookup th cx =
    Thin.proj th cx.tys

  let len cx =
    cx.len

  let env cx =
    cx.env

  let qctx cx =
    cx.qctx

end

type ctx = Ctx.t

let rec check ~mode ~ctx ~ty ~tm =
  match Val.out ty, Tm.out tm with
  | Val.Univ lvl, Tm.Univ lvl' ->
    if Lvl.greater lvl lvl' then () else failwith "Universe level failure"

  | Val.Univ _, Tm.Pi (dom, Tm.B cod) ->
    let vdom = check_eval ~mode ~ctx ~ty ~tm:dom in
    let ctx' = Ctx.ext ctx vdom in
    check ~mode ~ctx:ctx' ~ty ~tm:cod

  | Val.Univ _, Tm.Sg (dom, Tm.B cod) ->
    let vdom = check_eval ~mode ~ctx ~ty ~tm:dom in
    let ctx' = Ctx.ext ctx vdom in
    check ~mode ~ctx:ctx' ~ty ~tm:cod

  | Val.Univ _, Tm.Ext (tag, dom, sys) ->
    failwith "TODO!"

  | Val.Pi (dom, cod), Tm.Lam (Tm.B tm) ->
    let vdom = Val.eval_clo dom in
    let ctx' = Ctx.ext ctx vdom in
    let vgen = Val.generic vdom @@ Ctx.len ctx in
    let vcod = Val.inst_bclo cod vgen in
    check ~mode ~ctx:ctx' ~ty:vcod ~tm

  | Val.Sg (dom, cod), Tm.Cons (tm0, tm1) ->
    let vdom = Val.eval_clo dom in
    let vtm0 = check_eval ~mode ~ctx ~ty:vdom ~tm:tm0 in
    let vcod = Val.inst_bclo cod vtm0 in
    check ~mode ~ctx ~ty:vcod ~tm:tm1

  | Val.Ext (tag, dom, sys), _ ->
    failwith "TODO!"

  | Val.Interval _, Tm.Dim0 ->
    ()

  | Val.Interval _, Tm.Dim1 ->
    ()

  | _, Tm.Up tm ->
    let ty' = infer ~mode ~ctx ~tm in
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    Quote.approx ~ctx:(Ctx.qctx ctx) ~ty:univ ~can0:ty' ~can1:ty


  | _ -> failwith ""

and check_eval ~mode ~ctx ~ty ~tm =
  check ~mode ~ctx ~ty ~tm;
  Val.eval (Ctx.env ctx) tm


and infer ~mode ~ctx ~tm =
  match Tm.out tm with
  | Tm.Var th ->
    Ctx.lookup th ctx

  | Tm.App (tfun, targ) ->
    let ty = infer ~mode ~ctx ~tm:tfun in
    let dom, cod = Val.out_pi ty in
    let vdom = Val.eval_clo dom in
    let varg = check_eval ~mode ~ctx ~ty:vdom ~tm:targ in
    Val.inst_bclo cod varg

  | Tm.Car tm ->
    let ty = infer ~mode ~ctx ~tm in
    let dom, _ = Val.out_sg ty in
    Val.eval_clo dom

  | Tm.Cdr tm ->
    let ty = infer ~mode ~ctx ~tm in
    let _, cod = Val.out_sg ty in
    let vpair = Val.eval (Ctx.env ctx) tm in
    let vcar = Val.car vpair in
    Val.inst_bclo cod vcar

  | Tm.Down {ty; tm} ->
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    let vty = check_eval ~mode ~ctx ~ty:univ ~tm:ty in
    check ~mode ~ctx ~ty:vty ~tm;
    vty

  | Tm.Coe coe ->
    let interval = Val.into @@ Val.Interval coe.tag in
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    let vdim0 = check_eval ~mode ~ctx ~ty:interval ~tm:coe.dim0 in
    let vdim1 = check_eval ~mode ~ctx ~ty:interval ~tm:coe.dim1 in
    let Tm.B ty = coe.ty in
    let ty_mode = 
      match coe.tag with
      | Cube.Equality -> Irrel
      | Cube.Path -> mode
    in
    check ~mode:ty_mode ~ctx:(Ctx.ext ctx interval) ~ty:univ ~tm:ty;
    let vty0 = Val.eval (vdim0 :: Ctx.env ctx) ty in
    check ~mode ~ctx:ctx ~ty:vty0 ~tm:coe.tm;
    Val.eval (vdim1 :: Ctx.env ctx) ty

  | Tm.HCom hcom ->
    failwith ""

  | Tm.Com com ->
    failwith ""

  | _ -> failwith "pattern exhaustiveness + GADTs is broken in OCaml :("
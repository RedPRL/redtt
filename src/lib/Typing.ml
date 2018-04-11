module Ctx :
sig
  type t
  val emp : t
  val ext : t -> Val.can Val.t -> t

  include DimRel.S with type t := t

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
     rel : DimRel.M.t;
     len : int}

  let emp =
    {tys = [];
     env = Val.Env.emp;
     qctx = Quote.Ctx.emp;
     rel = DimRel.M.emp;
     len = 0}

  let ext cx v =
    {tys = v :: cx.tys;
     env = Val.Env.ext cx.env v;
     qctx = Quote.Ctx.ext cx.qctx v;
     rel = cx.rel;
     len = cx.len + 1}

  let restrict_exn cx d0 d1 =
    let rel = DimRel.M.restrict_exn cx.rel d0 d1 in
    {cx with rel = rel}

  let compare_dim cx =
    DimRel.M.compare_dim cx.rel

  exception Inconsistent = DimRel.M.Inconsistent

  let lookup th cx =
    Thin.proj th cx.tys

  let len cx =
    cx.len

  let env cx =
    cx.env

  let qctx cx =
    cx.qctx
end

let rec update_env ix v rho = 
  match ix, rho with
  | 0, _ :: rho -> v :: rho
  | _, v' :: rho -> v' :: update_env (ix - 1) v rho
  | _ -> failwith "update_env"

type mode = FaconDeParler | Real

module Mode =
struct
  type t = mode

  let ontologically_real = Real
  let facon_de_parler = FaconDeParler
end

type ctx = Ctx.t

let rec check ~mode ~ctx ~ty ~tm =
  match Val.out ty, Tm.out tm with
  | Val.Univ lvl, Tm.Univ lvl' ->
    if Lvl.greater lvl lvl' then () else failwith "Universe level failure"

  | Val.Univ _, Tm.Pi (dom, Tm.B cod) ->
    let vdom = check_eval ~mode:FaconDeParler ~ctx ~ty ~tm:dom in
    let ctx' = Ctx.ext ctx vdom in
    check ~mode:Real ~ctx:ctx' ~ty ~tm:cod

  | Val.Univ _, Tm.Sg (dom, Tm.B cod) ->
    let vdom = check_eval ~mode:Real ~ctx ~ty ~tm:dom in
    let ctx' = Ctx.ext ctx vdom in
    check ~mode:Real ~ctx:ctx' ~ty ~tm:cod

  | Val.Univ _, Tm.Restrict (tag, dom, sys) ->
    failwith "TODO!"

  | Val.Univ _, Tm.Interval tag ->
    begin
      match mode with
      | Real -> failwith "Interval is not ontologically real"
      | FaconDeParler -> ()
    end


  | Val.Pi (dom, cod), Tm.Lam (Tm.B tm) ->
    let vdom = Val.eval_clo dom in
    let ctx' = Ctx.ext ctx vdom in
    let vgen = Val.generic vdom @@ Ctx.len ctx in
    let vcod = Val.inst_bclo cod vgen in
    check ~mode:Real ~ctx:ctx' ~ty:vcod ~tm

  | Val.Sg (dom, cod), Tm.Cons (tm0, tm1) ->
    let vdom = Val.eval_clo dom in
    let vtm0 = check_eval ~mode:Real ~ctx ~ty:vdom ~tm:tm0 in
    let vcod = Val.inst_bclo cod vtm0 in
    check ~mode:Real ~ctx ~ty:vcod ~tm:tm1

  | Val.Restrict (tag, dom, sys), _ ->
    check ~mode:Real ~ctx ~ty:dom ~tm;
    let go (vd0, vd1, otclo) =
      try
        let ctx' = Ctx.restrict_exn ctx vd0 vd1 in
        let can0 = Val.eval (Ctx.env ctx') tm in
        let can1 = Val.eval_clo @@ Option.get_exn otclo in
        Quote.equiv ~ctx:(Ctx.qctx ctx') ~ty:dom ~can0 ~can1
      with
      | Ctx.Inconsistent -> ()
    in
    List.fold_right (fun tube _ -> go tube) sys ()

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
    let ty = infer ~mode:Real ~ctx ~tm:tfun in
    let dom, cod = Val.out_pi ty in
    let vdom = Val.eval_clo dom in
    let varg = check_eval ~mode:Real ~ctx ~ty:vdom ~tm:targ in
    Val.inst_bclo cod varg

  | Tm.Car tm ->
    let ty = infer ~mode:Real ~ctx ~tm in
    let dom, _ = Val.out_sg ty in
    Val.eval_clo dom

  | Tm.Cdr tm ->
    let ty = infer ~mode:Real ~ctx ~tm in
    let _, cod = Val.out_sg ty in
    let vpair = Val.eval (Ctx.env ctx) tm in
    let vcar = Val.car vpair in
    Val.inst_bclo cod vcar

  | Tm.Down {ty; tm} ->
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    let vty = check_eval ~mode:Real ~ctx ~ty:univ ~tm:ty in
    check ~mode:Real ~ctx ~ty:vty ~tm;
    vty

  | Tm.Coe coe ->
    let interval = Val.into @@ Val.Interval coe.tag in
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    let vdim0 = check_eval ~mode:Real ~ctx ~ty:interval ~tm:coe.dim0 in
    let vdim1 = check_eval ~mode:Real ~ctx ~ty:interval ~tm:coe.dim1 in
    let Tm.B ty = coe.ty in
    check ~mode:Real ~ctx:(Ctx.ext ctx interval) ~ty:univ ~tm:ty;
    let vty0 = Val.eval (Val.Env.ext (Ctx.env ctx) vdim0) ty in
    check ~mode:Real ~ctx:ctx ~ty:vty0 ~tm:coe.tm;
    Val.eval (Val.Env.ext (Ctx.env ctx) vdim1) ty

  | Tm.HCom hcom ->
    failwith ""

  | Tm.Com com ->
    failwith ""

  | _ -> failwith "pattern exhaustiveness + GADTs is broken in OCaml :("
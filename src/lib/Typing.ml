module Ctx :
sig
  type t
  val emp : t
  val ext : t -> Val.can Val.t -> t

  include DimRel.S with type t := t

  val lookup : int -> t -> Val.can Val.t
  val len : t -> int

  val env : t -> Val.env
  val qctx : t -> Quote.ctx
  val rel : t -> DimRel.t
end =
struct
  type t =
    {tys : Val.can Val.t list;
     env : Val.env;
     qctx : Quote.ctx;
     rel : DimRel.t;
     len : int}

  let emp =
    {tys = [];
     env = Val.Env.emp;
     qctx = Quote.Ctx.emp;
     rel = DimRel.emp;
     len = 0}

  let ext cx v =
    {tys = v :: cx.tys;
     env = Val.Env.ext cx.env @@ Val.generic v @@ cx.len;
     qctx = Quote.Ctx.ext cx.qctx v;
     rel = cx.rel;
     len = cx.len + 1}

  let restrict_exn cx d0 d1 =
    let rel = DimRel.restrict_exn cx.rel d0 d1 in
    {cx with rel = rel}

  let compare_dim cx =
    DimRel.compare_dim cx.rel

  exception Inconsistent = DimRel.Inconsistent

  let lookup i cx =
    List.nth cx.tys i

  let len cx = cx.len
  let env cx = Val.Env.set_rel cx.rel cx.env 
  let qctx cx = cx.qctx
  let rel cx = cx.rel
end

let rec update_env ix v rho =
  match ix, rho with
  | 0, _ :: rho -> v :: rho
  | _, v' :: rho -> v' :: update_env (ix - 1) v rho
  | _ -> failwith "update_env"

type ctx = Ctx.t

let check_sys_valid sys : unit =
  print_string "TODO: check favonia's validity condition on lists of equations\n"

let check_sys_valid_or_empty sys = 
  match sys with
  | [] -> ()
  | _ -> check_sys_valid sys

let rec check ~ctx ~ty ~tm =
  match Val.out ty, Tm.out tm with
  | Val.Univ lvl, Tm.Univ lvl' ->
    if Lvl.greater lvl lvl' then () else failwith "Universe level failure"

  | Val.Univ _, Tm.Pi (dom, Tm.B cod) ->
    let vdom = check_eval ~ctx ~ty ~tm:dom in
    let ctx' = Ctx.ext ctx vdom in
    check ~ctx:ctx' ~ty ~tm:cod

  | Val.Univ _, Tm.Sg (dom, Tm.B cod) ->
    let vdom = check_eval ~ctx ~ty ~tm:dom in
    let ctx' = Ctx.ext ctx vdom in
    check ~ctx:ctx' ~ty ~tm:cod

  | Val.Univ _, Tm.Ext (Tm.B (cod, sys)) ->
    check_sys_valid_or_empty sys;
    let interval = Val.into Val.Interval in
    let ctx' = Ctx.ext ctx interval in
    let vcod = check_eval ~ctx:ctx' ~ty ~tm:cod in
    check_sys ~ctx:ctx' ~ty:vcod ~sys

  | Val.Univ _, Tm.Bool ->
    ()

  | Val.Pi (dom, cod), Tm.Lam (Tm.B tm) ->
    let vdom = Val.eval_clo dom in
    let ctx' = Ctx.ext ctx vdom in
    let vgen = Val.generic vdom @@ Ctx.len ctx in
    let vcod = Val.inst_bclo cod vgen in
    check ~ctx:ctx' ~ty:vcod ~tm

  | Val.Ext (cod, sys), Tm.Lam (Tm.B tm) ->
    let interval = Val.into Val.Interval in
    let ctx' = Ctx.ext ctx interval in
    let vgen = Val.generic interval @@ Ctx.len ctx in
    let vcodx = Val.inst_bclo cod vgen in
    check ~ctx:ctx' ~ty:vcodx ~tm;
    let rec go sys =
      match sys with
      | [] -> 
        ()

      | tube :: sys ->
        match tube with
        | Val.Tube.True (_, clo) ->
          let can0 = Val.eval_clo clo in
          let can1 = Val.eval (Ctx.env ctx') tm in
          Quote.equiv ~ctx:(Ctx.qctx ctx') ~ty:vcodx ~can0 ~can1

        | Val.Tube.Indeterminate ((dim0, dim1), clo) ->
          let ctx'' = Ctx.restrict_exn ctx' dim0 dim1 in
          let can0 = Val.eval_clo clo in
          let can1 = Val.eval (Ctx.env ctx'') tm in
          Quote.equiv ~ctx:(Ctx.qctx ctx') ~ty:vcodx ~can0 ~can1

        | Val.Tube.False _ ->
          ()

        | Val.Tube.Delete ->
          ()
          
    in
    go @@ Val.inst_sclo sys @@ Val.project_dimval vgen

  | Val.Sg (dom, cod), Tm.Cons (tm0, tm1) ->
    let vdom = Val.eval_clo dom in
    let vtm0 = check_eval ~ctx ~ty:vdom ~tm:tm0 in
    let vcod = Val.inst_bclo cod vtm0 in
    check ~ctx ~ty:vcod ~tm:tm1

  | Val.Interval, (Tm.Dim0 | Tm.Dim1) ->
    ()

  | Val.Bool, (Tm.Ff | Tm.Tt) ->
    ()

  | _, Tm.Up tm ->
    let ty' = infer ~ctx ~tm in
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    Quote.approx ~ctx:(Ctx.qctx ctx) ~ty:univ ~can0:ty' ~can1:ty

  | _, _ -> failwith @@ "check: " ^ Val.to_string ty

and check_eval ~ctx ~ty ~tm =
  check ~ctx ~ty ~tm;
  Val.eval (Ctx.env ctx) tm


and infer ~ctx ~tm =
  match Tm.out tm with
  | Tm.Var th ->
    Ctx.lookup th ctx

  | Tm.FunApp (tfun, targ) ->
    let ty = infer ~ctx ~tm:tfun in
    let dom, cod = Val.out_pi ty in
    let vdom = Val.eval_clo dom in
    let varg = check_eval ~ctx ~ty:vdom ~tm:targ in
    Val.inst_bclo cod varg

  | Tm.ExtApp (text, targ) ->
    let ty = infer ~ctx ~tm:text in
    let cod, _ = Val.out_ext ty in
    let interval = Val.into Val.Interval in
    let varg = check_eval ~ctx ~ty:interval ~tm:targ in
    Val.inst_bclo cod varg

  | Tm.Car tm ->
    let ty = infer ~ctx ~tm in
    let dom, _ = Val.out_sg ty in
    Val.eval_clo dom

  | Tm.Cdr tm ->
    let ty = infer ~ctx ~tm in
    let _, cod = Val.out_sg ty in
    let vpair = Val.eval (Ctx.env ctx) tm in
    let vcar = Val.car vpair in
    Val.inst_bclo cod vcar

  | Tm.If {mot = Tm.B mot; scrut; tcase; fcase} ->
    let bool = Val.into Val.Bool in
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    let bool' = infer ~ctx ~tm:scrut in
    Quote.equiv ~ctx:(Ctx.qctx ctx) ~ty:univ ~can0:bool ~can1:bool';
    check ~ctx:(Ctx.ext ctx bool) ~ty:univ ~tm:mot;
    let tt = Val.into Val.Tt in
    let ff = Val.into Val.Ff in
    let env = Ctx.env ctx in
    let tmot = Val.eval (Val.Env.ext env tt) mot in
    check ~ctx ~ty:tmot ~tm:tcase;
    let fmot = Val.eval (Val.Env.ext env ff) mot in
    check ~ctx ~ty:fmot ~tm:fcase;
    let vscrut = Val.eval env scrut in
    Val.eval (Val.Env.ext env vscrut) mot

  | Tm.Down {ty; tm} ->
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    let vty = check_eval ~ctx ~ty:univ ~tm:ty in
    check ~ctx ~ty:vty ~tm;
    vty

  | Tm.Coe coe ->
    let interval = Val.into Val.Interval in
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    let vdim0 = check_eval ~ctx ~ty:interval ~tm:coe.dim0 in
    let vdim1 = check_eval ~ctx ~ty:interval ~tm:coe.dim1 in
    let Tm.B ty = coe.ty in
    check ~ctx:(Ctx.ext ctx interval) ~ty:univ ~tm:ty;
    let env = Ctx.env ctx in
    let vty0 = Val.eval (Val.Env.ext env vdim0) ty in
    check ~ctx:ctx ~ty:vty0 ~tm:coe.tm;
    Val.eval (Val.Env.ext env vdim1) ty

  | Tm.HCom hcom ->
    let interval = Val.into Val.Interval in
    let vdim0 = check_eval ~ctx ~ty:interval ~tm:hcom.dim0 in
    check ~ctx ~ty:interval ~tm:hcom.dim1;
    check_sys_valid hcom.sys;
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    let vty = check_eval ~ctx ~ty:univ ~tm:hcom.ty in
    let vcap = check_eval ~ctx ~ty:vty ~tm:hcom.cap in
    check_bsys ~ctx ~dim0:vdim0 ~tycap:vty ~ty:vty ~cap:vcap ~sys:hcom.sys;
    vty

  | Tm.Com com ->
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    let interval = Val.into Val.Interval in
    let vdim0 = check_eval ~ctx ~ty:interval ~tm:com.dim0 in
    let vdim1 = check_eval ~ctx ~ty:interval ~tm:com.dim1 in
    check_sys_valid com.sys;

    let Tm.B ty = com.ty in
    let vty = check_eval ~ctx:(Ctx.ext ctx interval) ~ty:univ ~tm:ty in
    let env = Ctx.env ctx in
    let vty0 = Val.eval (Val.Env.ext env vdim0) ty in
    let vcap = check_eval ~ctx ~ty:vty0 ~tm:com.cap in
    check_bsys ~ctx ~dim0:vdim0 ~tycap:vty0 ~ty:vty ~cap:vcap ~sys:com.sys;
    Val.eval (Val.Env.ext env vdim1) ty

  | _ -> failwith "pattern exhaustiveness + GADTs is broken in OCaml :("

and check_bsys ~ctx ~dim0 ~tycap ~ty ~cap ~sys =
  let interval = Val.into Val.Interval in
  let rec go sys acc =
    match sys with
    | [] ->
      ()

    | (td0, td1, tb) :: sys ->
      let vd0 = Val.project_dimval @@ check_eval ~ctx ~ty:interval ~tm:td0 in
      let vd1 = Val.project_dimval @@ check_eval ~ctx ~ty:interval ~tm:td1 in
      match Ctx.compare_dim ctx vd0 vd1, tb with
      | DimVal.Apart, None ->
        go sys acc

      | (DimVal.Same | DimVal.Indeterminate), Some (Tm.B tb) ->
        let ctx' = Ctx.ext ctx interval in
        let ctx'' = Ctx.restrict_exn ctx' vd0 vd1 in
        check ~ctx:ctx'' ~ty:ty ~tm:tb;

        let env = Ctx.env ctx'' in
        let vtb = Val.eval (Val.Env.ext env dim0) tb in

        (* Check cap-tube compatibility *)
        Quote.equiv ~ctx:(Ctx.qctx ctx'') ~ty ~can0:cap ~can1:vtb;

        (* Check tube-tube adjacency conditions *)
        go_adj ctx'' acc (vd0, vd1, tb);
        go sys @@ (vd0, vd1, tb) :: acc

      | _ ->
        failwith "check_bsys"

  (* Invariant: 'ctx' should already be restricted by vd0=vd1 *)
  and go_adj ctx tubes (vd0, vd1, tb) = 
    match tubes with
    | [] ->
      ()

    | (vd0', vd1', tb') :: tubes ->
      let ctx' = Ctx.restrict_exn ctx vd0' vd1' in
      let env = Ctx.env ctx' in
      let vtb = Val.eval env tb in
      let vtb' = Val.eval env tb' in
      Quote.equiv ~ctx:(Ctx.qctx ctx) ~ty ~can0:vtb ~can1:vtb';
      go_adj ctx tubes (vd0, vd1, tb)

  in
  go sys []

and check_sys ~ctx ~ty ~sys =
  let interval = Val.into Val.Interval in
  let rec go sys acc =
    match sys with
    | [] ->
      ()

    | (td0, td1, tb) :: sys ->
      let vd0 = Val.project_dimval @@ check_eval ~ctx ~ty:interval ~tm:td0 in
      let vd1 = Val.project_dimval @@ check_eval ~ctx ~ty:interval ~tm:td1 in
      match Ctx.compare_dim ctx vd0 vd1, tb with
      | DimVal.Apart, None ->
        go sys acc

      | (DimVal.Same | DimVal.Indeterminate), Some tb ->
        let ctx' = Ctx.restrict_exn ctx vd0 vd1 in
        check ~ctx:ctx' ~ty ~tm:tb;

        (* Check tube-tube adjacency conditions *)
        go_adj ctx' acc (vd0, vd1, tb);
        go sys @@ (vd0, vd1, tb) :: acc

      | _ ->
        failwith "check_bsys"

  (* Invariant: 'ctx' should already be restricted by vd0=vd1 *)
  and go_adj ctx tubes (vd0, vd1, tb) = 
    match tubes with
    | [] ->
      ()

    | (vd0', vd1', tb') :: tubes ->
      let ctx' = Ctx.restrict_exn ctx vd0' vd1' in
      let env = Ctx.env ctx' in
      let vtb = Val.eval env tb in
      let vtb' = Val.eval env tb' in
      Quote.equiv ~ctx:(Ctx.qctx ctx) ~ty ~can0:vtb ~can1:vtb';
      go_adj ctx tubes (vd0, vd1, tb)

  in
  go sys []
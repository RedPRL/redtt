module Ctx = LCx

type cx = Ctx.t

let check_sys_valid sys : unit =
  print_string "TODO: check favonia's validity condition on lists of equations\n"

let check_sys_valid_or_empty sys = 
  match sys with
  | [] -> ()
  | _ -> check_sys_valid sys

let rec check ~cx ~ty ~tm =
  match Val.out ty, Tm.out tm with
  | Val.Univ lvl, Tm.Univ lvl' ->
    if Lvl.greater lvl lvl' then () else failwith "Universe level failure"

  | Val.Univ _, Tm.Pi (dom, Tm.B cod) ->
    let vdom = check_eval ~cx ~ty ~tm:dom in
    let cx' = Ctx.ext cx vdom in
    check ~cx:cx' ~ty ~tm:cod

  | Val.Univ _, Tm.Sg (dom, Tm.B cod) ->
    let vdom = check_eval ~cx ~ty ~tm:dom in
    let cx' = Ctx.ext cx vdom in
    check ~cx:cx' ~ty ~tm:cod

  | Val.Univ _, Tm.Ext (Tm.B (cod, sys)) ->
    check_sys_valid_or_empty sys;
    let interval = Val.into Val.Interval in
    let cx' = Ctx.ext cx interval in
    let vcod = check_eval ~cx:cx' ~ty ~tm:cod in
    check_sys ~cx:cx' ~ty:vcod ~sys

  | Val.Univ _, Tm.Bool ->
    ()

  | Val.Pi (dom, cod), Tm.Lam (Tm.B tm) ->
    let vdom = Val.eval_clo dom in
    let cx' = Ctx.ext cx vdom in
    let vgen = Val.generic vdom @@ Ctx.len cx in
    let vcod = Val.inst_bclo cod vgen in
    check ~cx:cx' ~ty:vcod ~tm

  | Val.Ext (cod, sys), Tm.Lam (Tm.B tm) ->
    let interval = Val.into Val.Interval in
    let cx' = Ctx.ext cx interval in
    let vgen = Val.generic interval @@ Ctx.len cx in
    let vcodx = Val.inst_bclo cod vgen in
    check ~cx:cx' ~ty:vcodx ~tm;
    let rec go sys =
      match sys with
      | [] -> 
        ()

      | tube :: sys ->
        match tube with
        | Val.Tube.True (_, clo) ->
          let can0 = Val.eval_clo clo in
          let can1 = Val.eval (Ctx.env cx') tm in
          Quote.equiv ~n:(Ctx.len cx') ~ty:vcodx ~can0 ~can1

        | Val.Tube.Indeterminate ((dim0, dim1), clo) ->
          let cx'' = Ctx.restrict_exn cx' dim0 dim1 in
          let can0 = Val.eval_clo clo in
          let can1 = Val.eval (Ctx.env cx'') tm in
          Quote.equiv ~n:(Ctx.len cx'') ~ty:vcodx ~can0 ~can1

        | Val.Tube.False _ ->
          ()

        | Val.Tube.Delete ->
          ()

    in
    go @@ Val.inst_sclo sys @@ Val.project_dimval vgen

  | Val.Sg (dom, cod), Tm.Cons (tm0, tm1) ->
    let vdom = Val.eval_clo dom in
    let vtm0 = check_eval ~cx ~ty:vdom ~tm:tm0 in
    let vcod = Val.inst_bclo cod vtm0 in
    check ~cx ~ty:vcod ~tm:tm1

  | Val.Interval, (Tm.Dim0 | Tm.Dim1) ->
    ()

  | Val.Bool, (Tm.Ff | Tm.Tt) ->
    ()

  | _, Tm.Up tm ->
    let ty' = infer ~cx ~tm in
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    Quote.approx ~n:(Ctx.len cx) ~ty:univ ~can0:ty' ~can1:ty

  | _, Tm.Let (tm0, Tm.B tm1) ->
    let ty0 = infer ~cx ~tm:tm0 in
    let v = Val.eval (Ctx.env cx) tm0 in
    let cx' = Ctx.def cx ~ty:ty0 ~tm:v in
    check ~cx:cx' ~ty ~tm:tm1

  | _, _ -> failwith @@ "check: " ^ Val.to_string ty

and check_eval ~cx ~ty ~tm =
  check ~cx ~ty ~tm;
  Val.eval (Ctx.env cx) tm


and infer ~cx ~tm =
  match Tm.out tm with
  | Tm.Var th ->
    Ctx.lookup th cx

  | Tm.FunApp (tfun, targ) ->
    let ty = infer ~cx ~tm:tfun in
    let dom, cod = Val.out_pi ty in
    let vdom = Val.eval_clo dom in
    let varg = check_eval ~cx ~ty:vdom ~tm:targ in
    Val.inst_bclo cod varg

  | Tm.ExtApp (text, targ) ->
    let ty = infer ~cx ~tm:text in
    let cod, _ = Val.out_ext ty in
    let interval = Val.into Val.Interval in
    let varg = check_eval ~cx ~ty:interval ~tm:targ in
    Val.inst_bclo cod varg

  | Tm.Car tm ->
    let ty = infer ~cx ~tm in
    let dom, _ = Val.out_sg ty in
    Val.eval_clo dom

  | Tm.Cdr tm ->
    let ty = infer ~cx ~tm in
    let _, cod = Val.out_sg ty in
    let vpair = Val.eval (Ctx.env cx) tm in
    let vcar = Val.car vpair in
    Val.inst_bclo cod vcar

  | Tm.If {mot = Tm.B mot; scrut; tcase; fcase} ->
    let bool = Val.into Val.Bool in
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    let bool' = infer ~cx ~tm:scrut in
    Quote.equiv ~n:(Ctx.len cx) ~ty:univ ~can0:bool ~can1:bool';
    check ~cx:(Ctx.ext cx bool) ~ty:univ ~tm:mot;
    let tt = Val.into Val.Tt in
    let ff = Val.into Val.Ff in
    let env = Ctx.env cx in
    let tmot = Val.eval (Val.Env.ext env tt) mot in
    check ~cx ~ty:tmot ~tm:tcase;
    let fmot = Val.eval (Val.Env.ext env ff) mot in
    check ~cx ~ty:fmot ~tm:fcase;
    let vscrut = Val.eval env scrut in
    Val.eval (Val.Env.ext env vscrut) mot

  | Tm.Down {ty; tm} ->
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    let vty = check_eval ~cx ~ty:univ ~tm:ty in
    check ~cx ~ty:vty ~tm;
    vty

  | Tm.Coe coe ->
    let interval = Val.into Val.Interval in
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    let vdim0 = check_eval ~cx ~ty:interval ~tm:coe.dim0 in
    let vdim1 = check_eval ~cx ~ty:interval ~tm:coe.dim1 in
    let Tm.B ty = coe.ty in
    check ~cx:(Ctx.ext cx interval) ~ty:univ ~tm:ty;
    let env = Ctx.env cx in
    let vty0 = Val.eval (Val.Env.ext env vdim0) ty in
    check ~cx:cx ~ty:vty0 ~tm:coe.tm;
    Val.eval (Val.Env.ext env vdim1) ty

  | Tm.HCom hcom ->
    let interval = Val.into Val.Interval in
    let vdim0 = check_eval ~cx ~ty:interval ~tm:hcom.dim0 in
    check ~cx ~ty:interval ~tm:hcom.dim1;
    check_sys_valid hcom.sys;
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    let vty = check_eval ~cx ~ty:univ ~tm:hcom.ty in
    let vcap = check_eval ~cx ~ty:vty ~tm:hcom.cap in
    check_bsys ~cx ~dim0:vdim0 ~tycap:vty ~ty:vty ~cap:vcap ~sys:hcom.sys;
    vty

  | Tm.Com com ->
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    let interval = Val.into Val.Interval in
    let vdim0 = check_eval ~cx ~ty:interval ~tm:com.dim0 in
    let vdim1 = check_eval ~cx ~ty:interval ~tm:com.dim1 in
    check_sys_valid com.sys;

    let Tm.B ty = com.ty in
    let vty = check_eval ~cx:(Ctx.ext cx interval) ~ty:univ ~tm:ty in
    let env = Ctx.env cx in
    let vty0 = Val.eval (Val.Env.ext env vdim0) ty in
    let vcap = check_eval ~cx ~ty:vty0 ~tm:com.cap in
    check_bsys ~cx ~dim0:vdim0 ~tycap:vty0 ~ty:vty ~cap:vcap ~sys:com.sys;
    Val.eval (Val.Env.ext env vdim1) ty

  | Tm.Meta (sym, sigma) -> 
    failwith "TODO: typecheck meta"

  | _ -> failwith "pattern exhaustiveness + GADTs is broken in OCaml :("

and infer_subst ~cx ~subst =
  match subst with
  | Tm.Id ->
    cx

  | Tm.Proj ->
    Ctx.proj cx

  | Tm.Cmp (tau, sigma) ->
    let cx' = infer_subst ~cx ~subst:sigma in
    infer_subst ~cx:cx' ~subst:tau

  | Tm.Sub (sigma, t) ->
    let ty = infer ~cx ~tm:t in
    let cx' = infer_subst ~cx ~subst:sigma in
    let el = Val.eval (Ctx.env cx) t in
    Ctx.def cx' ~ty ~tm:el


and check_bsys ~cx ~dim0 ~tycap ~ty ~cap ~sys =
  let interval = Val.into Val.Interval in
  let rec go sys acc =
    match sys with
    | [] ->
      ()

    | (td0, td1, tb) :: sys ->
      let vd0 = Val.project_dimval @@ check_eval ~cx ~ty:interval ~tm:td0 in
      let vd1 = Val.project_dimval @@ check_eval ~cx ~ty:interval ~tm:td1 in
      match Ctx.compare_dim cx vd0 vd1, tb with
      | DimVal.Apart, None ->
        go sys acc

      | (DimVal.Same | DimVal.Indeterminate), Some (Tm.B tb) ->
        let cx' = Ctx.ext cx interval in
        let cx'' = Ctx.restrict_exn cx' vd0 vd1 in
        check ~cx:cx'' ~ty:ty ~tm:tb;

        let env = Ctx.env cx'' in
        let vtb = Val.eval (Val.Env.ext env dim0) tb in

        (* Check cap-tube compatibility *)
        Quote.equiv ~n:(Ctx.len cx'') ~ty ~can0:cap ~can1:vtb;

        (* Check tube-tube adjacency conditions *)
        go_adj cx'' acc (vd0, vd1, tb);
        go sys @@ (vd0, vd1, tb) :: acc

      | _ ->
        failwith "check_bsys"

  (* Invariant: 'cx' should already be restricted by vd0=vd1 *)
  and go_adj cx tubes (vd0, vd1, tb) = 
    match tubes with
    | [] ->
      ()

    | (vd0', vd1', tb') :: tubes ->
      let cx' = Ctx.restrict_exn cx vd0' vd1' in
      let env = Ctx.env cx' in
      let vtb = Val.eval env tb in
      let vtb' = Val.eval env tb' in
      Quote.equiv ~n:(Ctx.len cx) ~ty ~can0:vtb ~can1:vtb';
      go_adj cx tubes (vd0, vd1, tb)

  in
  go sys []

and check_sys ~cx ~ty ~sys =
  let interval = Val.into Val.Interval in
  let rec go sys acc =
    match sys with
    | [] ->
      ()

    | (td0, td1, tb) :: sys ->
      let vd0 = Val.project_dimval @@ check_eval ~cx ~ty:interval ~tm:td0 in
      let vd1 = Val.project_dimval @@ check_eval ~cx ~ty:interval ~tm:td1 in
      match Ctx.compare_dim cx vd0 vd1, tb with
      | DimVal.Apart, None ->
        go sys acc

      | (DimVal.Same | DimVal.Indeterminate), Some tb ->
        let cx' = Ctx.restrict_exn cx vd0 vd1 in
        check ~cx:cx' ~ty ~tm:tb;

        (* Check tube-tube adjacency conditions *)
        go_adj cx' acc (vd0, vd1, tb);
        go sys @@ (vd0, vd1, tb) :: acc

      | _ ->
        failwith "check_bsys"

  (* Invariant: 'cx' should already be restricted by vd0=vd1 *)
  and go_adj cx tubes (vd0, vd1, tb) = 
    match tubes with
    | [] ->
      ()

    | (vd0', vd1', tb') :: tubes ->
      begin
        try 
          let cx' = Ctx.restrict_exn cx vd0' vd1' in
          let env = Ctx.env cx' in
          let vtb = Val.eval env tb in
          let vtb' = Val.eval env tb' in
          Quote.equiv ~n:(Ctx.len cx') ~ty ~can0:vtb ~can1:vtb';
        with
        | Ctx.Inconsistent -> ()
      end;
      go_adj cx tubes (vd0, vd1, tb)

  in
  go sys []
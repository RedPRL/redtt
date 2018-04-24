type cx = LCx.t
type mcx = MCx.t

let check_sys_valid sys : unit =
  print_string "TODO: check favonia's validity condition on lists of equations\n"

let check_sys_valid_or_empty sys =
  match sys with
  | [] -> ()
  | _ -> check_sys_valid sys

let rec check ~mcx ~cx ~ty ~tm =
  match Val.out ty, Tm.out tm with
  | Val.Univ lvl, Tm.Univ lvl' ->
    if Lvl.greater lvl lvl' then () else failwith "Universe level failure"

  | Val.Univ _, Tm.Pi (dom, Tm.B (nm, cod)) ->
    let vdom = check_eval ~mcx ~cx ~ty ~tm:dom in
    let cx' = LCx.ext cx ~nm vdom in
    check ~mcx ~cx:cx' ~ty ~tm:cod

  | Val.Univ _, Tm.Sg (dom, Tm.B (nm, cod)) ->
    let vdom = check_eval ~mcx ~cx ~ty ~tm:dom in
    let cx' = LCx.ext cx ~nm vdom in
    check ~mcx ~cx:cx' ~ty ~tm:cod

  | Val.Univ _, Tm.Ext (Tm.B (nm, (cod, sys))) ->
    check_sys_valid_or_empty sys;
    let interval = Val.into Val.Interval in
    let cx' = LCx.ext cx ~nm interval in
    let vcod = check_eval ~mcx ~cx:cx' ~ty ~tm:cod in
    check_sys ~mcx ~cx:cx' ~ty:vcod ~sys

  | Val.Univ _, Tm.Bool ->
    ()

  | Val.Pi (dom, cod), Tm.Lam (Tm.B (nm, tm)) ->
    let vdom = Val.eval_clo dom in
    let cx' = LCx.ext cx ~nm vdom in
    let vgen = Val.generic vdom @@ LCx.len cx in
    let vcod = Val.inst_bclo cod vgen in
    check ~mcx ~cx:cx' ~ty:vcod ~tm

  | Val.Ext (cod, sys), Tm.Lam (Tm.B (nm, tm)) ->
    let interval = Val.into Val.Interval in
    let cx' = LCx.ext cx ~nm interval in
    let vgen = Val.generic interval @@ LCx.len cx in
    let vcodx = Val.inst_bclo cod vgen in
    check ~mcx ~cx:cx' ~ty:vcodx ~tm;
    let rec go sys =
      match sys with
      | [] ->
        ()

      | tube :: sys ->
        match tube with
        | Val.Tube.True (_, clo) ->
          let can0 = Val.eval_clo clo in
          let can1 = Val.eval (MCx.menv mcx, LCx.env cx') tm in
          equiv "ext/lam/tube/true" ~cx:cx' ~ty:vcodx can0 can1;
          go sys

        | Val.Tube.Indeterminate ((dim0, dim1), clo) ->
          let cx'' = LCx.restrict_exn cx' dim0 dim1 in
          let can0 = Val.eval_clo clo in
          let can1 = Val.eval (MCx.menv mcx, LCx.env cx'') tm in
          equiv "ext/lam/tube/indet" ~cx:cx'' ~ty:vcodx can0 can1;
          go sys

        | Val.Tube.False _ ->
          Format.fprintf Format.err_formatter "Found false tube@.";
          go sys

        | Val.Tube.Delete ->
          Format.fprintf Format.err_formatter "Found delete tube@.";
          go sys

    in
    go @@ Val.inst_sclo sys @@ Val.project_dimval vgen

  | Val.Sg (dom, cod), Tm.Cons (tm0, tm1) ->
    let vdom = Val.eval_clo dom in
    let vtm0 = check_eval ~mcx ~cx ~ty:vdom ~tm:tm0 in
    let vcod = Val.inst_bclo cod vtm0 in
    check ~mcx ~cx ~ty:vcod ~tm:tm1

  | Val.Interval, (Tm.Dim0 | Tm.Dim1) ->
    ()

  | Val.Bool, (Tm.Ff | Tm.Tt) ->
    ()

  | _, Tm.Up tm ->
    let ty' = infer ~mcx ~cx ~tm in
    approx_ty ~cx:cx ty' ty

  | _, Tm.Let (tm0, Tm.B (_, tm1)) ->
    let ty0 = infer ~mcx ~cx ~tm:tm0 in
    let v = Val.eval (MCx.menv mcx, LCx.env cx) tm0 in
    let cx' = LCx.def cx ty0 v in
    check ~mcx ~cx:cx' ~ty ~tm:tm1

  | _, _ ->
    let ppenv = LCx.ppenv cx in
    let n = LCx.len cx in
    let tty = Quote.quote_ty n ty in
    Format.fprintf Format.err_formatter "%a !: %a" (Tm.pp ppenv) tm (Tm.pp ppenv) tty;
    failwith "check"

and check_eval ~mcx ~cx ~ty ~tm =
  check ~mcx ~cx ~ty ~tm;
  Val.eval (MCx.menv mcx, LCx.env cx) tm


and infer ~mcx ~cx ~tm =
  match Tm.out tm with
  | Tm.Var th ->
    LCx.lookup th cx

  | Tm.FunApp (tfun, targ) ->
    let ty = infer ~mcx ~cx ~tm:tfun in
    let dom, cod = Val.out_pi ty in
    let vdom = Val.eval_clo dom in
    let varg = check_eval ~mcx ~cx ~ty:vdom ~tm:targ in
    Val.inst_bclo cod varg

  | Tm.ExtApp (text, targ) ->
    let ty = infer ~mcx ~cx ~tm:text in
    let cod, _ = Val.out_ext ty in
    let interval = Val.into Val.Interval in
    let varg = check_eval ~mcx ~cx ~ty:interval ~tm:targ in
    Val.inst_bclo cod varg

  | Tm.Car tm ->
    let ty = infer ~mcx ~cx ~tm in
    let dom, _ = Val.out_sg ty in
    Val.eval_clo dom

  | Tm.Cdr tm ->
    let ty = infer ~mcx ~cx ~tm in
    let _, cod = Val.out_sg ty in
    let vpair = Val.eval (MCx.menv mcx, LCx.env cx) tm in
    let vcar = Val.car vpair in
    Val.inst_bclo cod vcar

  | Tm.If {mot = Tm.B (nm, mot); scrut; tcase; fcase} ->
    let bool = Val.into Val.Bool in
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    let bool' = infer ~mcx ~cx ~tm:scrut in
    equiv "if" ~cx:cx ~ty:univ bool bool';
    check ~mcx ~cx:(LCx.ext cx ~nm bool) ~ty:univ ~tm:mot;
    let tt = Val.into Val.Tt in
    let ff = Val.into Val.Ff in
    let env = LCx.env cx in
    let tmot = Val.eval (MCx.menv mcx, Val.Env.ext env tt) mot in
    check ~mcx ~cx ~ty:tmot ~tm:tcase;
    let fmot = Val.eval (MCx.menv mcx, Val.Env.ext env ff) mot in
    check ~mcx ~cx ~ty:fmot ~tm:fcase;
    let vscrut = Val.eval (MCx.menv mcx, env) scrut in
    Val.eval (MCx.menv mcx, Val.Env.ext env vscrut) mot

  | Tm.Down {ty; tm} ->
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    let vty = check_eval ~mcx ~cx ~ty:univ ~tm:ty in
    check ~mcx ~cx ~ty:vty ~tm;
    vty

  | Tm.Coe coe ->
    let interval = Val.into Val.Interval in
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    let vdim0 = check_eval ~mcx ~cx ~ty:interval ~tm:coe.dim0 in
    let vdim1 = check_eval ~mcx ~cx ~ty:interval ~tm:coe.dim1 in
    let Tm.B (nm, ty) = coe.ty in
    check ~mcx ~cx:(LCx.ext cx ~nm interval) ~ty:univ ~tm:ty;
    let env = LCx.env cx in
    let vty0 = Val.eval (MCx.menv mcx, Val.Env.ext env vdim0) ty in
    check ~mcx ~cx:cx ~ty:vty0 ~tm:coe.tm;
    Val.eval (MCx.menv mcx, Val.Env.ext env vdim1) ty

  | Tm.HCom hcom ->
    let interval = Val.into Val.Interval in
    let vdim0 = check_eval ~mcx ~cx ~ty:interval ~tm:hcom.dim0 in
    check ~mcx ~cx ~ty:interval ~tm:hcom.dim1;
    check_sys_valid hcom.sys;
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    let vty = check_eval ~mcx ~cx ~ty:univ ~tm:hcom.ty in
    check_bsys ~mcx ~cx ~dim0:vdim0 ~tycap:vty ~ty:vty ~cap:hcom.cap ~sys:hcom.sys;
    vty

  | Tm.Com com ->
    let univ = Val.into @@ Val.Univ Lvl.Omega in
    let interval = Val.into Val.Interval in
    let vdim0 = check_eval ~mcx ~cx ~ty:interval ~tm:com.dim0 in
    let vdim1 = check_eval ~mcx ~cx ~ty:interval ~tm:com.dim1 in
    check_sys_valid com.sys;

    let Tm.B (nm, ty) = com.ty in
    let vty = check_eval ~mcx ~cx:(LCx.ext cx ~nm interval) ~ty:univ ~tm:ty in
    let env = LCx.env cx in
    let vty0 = Val.eval (MCx.menv mcx, Val.Env.ext env vdim0) ty in
    check_bsys ~mcx ~cx ~dim0:vdim0 ~tycap:vty0 ~ty:vty ~cap:com.cap ~sys:com.sys;
    Val.eval (MCx.menv mcx, Val.Env.ext env vdim1) ty

  | Tm.Meta (sym, sigma) ->
    let seq = MCx.lookup_exn sym mcx in
    let cx' = infer_subst ~mcx ~cx:seq.lcx ~subst:sigma in
    cx_equiv ~mcx ~cx0:cx ~cx1:cx';
    let env' = Val.eval_subst (MCx.menv mcx, LCx.env cx) sigma in
    Val.eval (MCx.menv mcx, env') seq.ty

  | _ -> failwith "pattern exhaustiveness + GADTs is broken in OCaml :("

and cx_equiv ~mcx ~cx0 ~cx1 =
  let univ = Val.into @@ Val.Univ Lvl.Omega in
  match LCx.view cx0, LCx.view cx1 with
  | LCx.Nil, LCx.Nil ->
    ()

  | LCx.Snoc snoc0, LCx.Snoc snoc1 ->
    cx_equiv ~mcx ~cx0:snoc0.cx ~cx1:snoc1.cx;
    equiv "cx_equiv" ~cx:snoc0.cx ~ty:univ snoc0.ty snoc1.ty;
    equiv "cx_equiv" ~cx:snoc0.cx ~ty:snoc0.ty snoc0.def snoc1.def

  | _ ->
    failwith "cx_equiv"

and infer_subst ~mcx ~cx ~subst =
  match subst with
  | Tm.Id ->
    cx

  | Tm.Proj ->
    LCx.proj_exn cx

  | Tm.Cmp (tau, sigma) ->
    let cx' = infer_subst ~mcx ~cx ~subst:sigma in
    infer_subst ~mcx ~cx:cx' ~subst:tau

  | Tm.Sub (sigma, t) ->
    let ty = infer ~mcx ~cx ~tm:t in
    let cx' = infer_subst ~mcx ~cx ~subst:sigma in
    let el = Val.eval (MCx.menv mcx, LCx.env cx) t in
    LCx.def cx' ty el


and check_bsys ~mcx ~cx ~dim0 ~tycap ~ty ~cap ~sys =
  let interval = Val.into Val.Interval in
  let rec go sys acc =
    match sys with
    | [] ->
      ()

    | (td0, td1, tb) :: sys ->
      let vd0 = Val.project_dimval @@ check_eval ~mcx ~cx ~ty:interval ~tm:td0 in
      let vd1 = Val.project_dimval @@ check_eval ~mcx ~cx ~ty:interval ~tm:td1 in
      match LCx.compare_dim cx vd0 vd1, tb with
      | DimVal.Apart, None ->
        go sys acc

      | (DimVal.Same | DimVal.Indeterminate), Some (Tm.B (nm, tb)) ->
        begin
          let cxx = LCx.restrict_exn (LCx.ext cx ~nm interval) vd0 vd1 in
          check ~mcx ~cx:cxx ~ty:ty ~tm:tb
        end;

        let cx0 = LCx.restrict_exn (LCx.def cx interval dim0) vd0 vd1 in
        let vtb = Val.eval (MCx.menv mcx, LCx.env cx0) tb in

        let vcap =
          let env = LCx.env @@ LCx.restrict_exn cx vd0 vd1 in
          Val.eval (MCx.menv mcx, env) cap
        in

        (* Check cap-tube compatibility *)
        equiv "bsys/cap-tube" ~cx:cx0 ~ty vcap vtb;

        (* Check tube-tube adjacency conditions *)
        go_adj (LCx.restrict_exn cx vd0 vd1) acc (vd0, vd1, tb);
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
          let cx' = LCx.restrict_exn cx vd0' vd1' in
          let env = LCx.env cx' in
          let vtb = Val.eval (MCx.menv mcx, env) tb in
          let vtb' = Val.eval (MCx.menv mcx, env) tb' in
          equiv "bsys/adj" ~cx:cx' ~ty vtb vtb';
        with
        | LCx.Inconsistent -> ()
      end;
      go_adj cx tubes (vd0, vd1, tb)

  in
  go sys []

and check_sys ~mcx ~cx ~ty ~sys =
  let interval = Val.into Val.Interval in
  let rec go sys acc =
    match sys with
    | [] ->
      ()

    | (td0, td1, tb) :: sys ->
      let vd0 = Val.project_dimval @@ check_eval ~mcx ~cx ~ty:interval ~tm:td0 in
      let vd1 = Val.project_dimval @@ check_eval ~mcx ~cx ~ty:interval ~tm:td1 in
      match LCx.compare_dim cx vd0 vd1, tb with
      | DimVal.Apart, None ->
        go sys acc

      | (DimVal.Same | DimVal.Indeterminate), Some tb ->
        let cx' = LCx.restrict_exn cx vd0 vd1 in
        check ~mcx ~cx:cx' ~ty ~tm:tb;

        (* Check tube-tube adjacency conditions *)
        go_adj cx' acc (vd0, vd1, tb);
        go sys @@ (vd0, vd1, tb) :: acc

      | _ ->
        failwith "check_sys"

  (* Invariant: 'cx' should already be restricted by vd0=vd1 *)
  and go_adj cx tubes (vd0, vd1, tb) =
    match tubes with
    | [] ->
      ()

    | (vd0', vd1', tb') :: tubes ->
      begin
        try
          let cx' = LCx.restrict_exn cx vd0' vd1' in
          let env = LCx.env cx' in
          let vtb = Val.eval (MCx.menv mcx, env) tb in
          let vtb' = Val.eval (MCx.menv mcx, env) tb' in
          equiv "sys/adj" ~cx:cx' ~ty vtb vtb';
        with
        | LCx.Inconsistent -> ()
      end;
      go_adj cx tubes (vd0, vd1, tb)

  in
  go sys []

and equiv trace ~cx ~ty can0 can1 =
  let ppenv = LCx.ppenv cx in
  let n = LCx.len cx in
  try
    ignore @@ Quote.equiv n ~ty can0 can1
  with
  | exn ->
    let tm0 = Quote.quote n ~ty can0 in
    let tm1 = Quote.quote n ~ty can1 in
    Format.fprintf Format.err_formatter "%s: checking %a == %a@." trace (Tm.pp ppenv) tm0 (Tm.pp ppenv) tm1;
    raise exn

and approx_ty ~cx ty0 ty1 =
  let ppenv = LCx.ppenv cx in
  let n = LCx.len cx in
  try
    ignore @@ Quote.approx_ty n ty0 ty1
  with
  | exn ->
    let tm0 = Quote.quote_ty n ty0 in
    let tm1 = Quote.quote_ty n ty1 in
    Format.fprintf Format.err_formatter "%a /<= %a\n" (Tm.pp ppenv) tm0 (Tm.pp ppenv) tm1;
    raise exn

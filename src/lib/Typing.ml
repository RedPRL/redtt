module D = Val

let rec check ~ctx ~ty ~tm =
  match ty, tm with
  | D.U `Omega, Tm.U _ ->
    ()

  | D.U (`Const lvl), Tm.U lvl' ->
    if lvl' < lvl then () else failwith "[check]: universe level error"

  | D.U _, Tm.Unit ->
    ()

  | D.U _, Tm.Bool ->
    ()

  | D.U _, Tm.Pi (dom, Tm.B cod) ->
    let vdom = check_eval ~ctx ~ty ~tm:dom in
    let ctx', _ = Ctx.add ~ctx ~ty:vdom in
    check ~ctx:ctx' ~ty ~tm:cod

  | D.U _, Tm.Sg (dom, Tm.B cod) ->
    let vdom = check_eval ~ctx ~ty ~tm:dom in
    let ctx', _ = Ctx.add ~ctx ~ty:vdom in
    check ~ctx:ctx' ~ty ~tm:cod

  | D.U _, Tm.Eq (Tm.B cod, t0, t1) ->
    let ctxi, _ = Ctx.add ~ctx ~ty:D.Interval in
    check ~ctx:ctxi ~ty ~tm:cod;
    let vcod0 = Sem.eval (D.Dim0 :: Ctx.env ctx) cod in
    check ~ctx:ctx ~ty:vcod0 ~tm:t0;
    let vcod1 = Sem.eval (D.Dim1 :: Ctx.env ctx) cod in
    check ~ctx:ctx ~ty:vcod1 ~tm:t1


  | D.Unit, Tm.Ax ->
    ()

  | D.Bool, Tm.Tt ->
    ()

  | D.Bool, Tm.Ff ->
    ()

  | D.Interval, Tm.Dim0 ->
    ()

  | D.Interval, Tm.Dim1 ->
    ()

  | D.Pi (vdom, vcod), Tm.Lam (Tm.B bdy) ->
    let ctx', atom = Ctx.add ~ctx ~ty:vdom in
    let vcod' = Sem.apply vcod atom in
    check ~ctx:ctx' ~ty:vcod' ~tm:bdy

  | D.Sg (vdom, vcod), Tm.Pair (t1, t2) ->
    let v1 = check_eval ~ctx ~ty:vdom ~tm:t1 in
    let vcod' = Sem.apply vcod v1 in
    check ~ctx:ctx ~ty:vcod' ~tm:t2

  | D.Eq (vcod, v0, v1), Tm.Lam (Tm.B bdy) ->
    let ctxi, atom = Ctx.add ~ctx ~ty:D.Interval in
    let vcodi = Sem.apply vcod atom in
    check ~ctx:ctxi ~ty:vcodi ~tm:bdy;
    let vbdy0 = Sem.eval (D.Dim0 :: Ctx.env ctx) bdy in
    let vbdy1 = Sem.eval (D.Dim1 :: Ctx.env ctx) bdy in
    check_eq ~ctx:ctx ~ty:(Sem.apply vcod D.Dim0) ~lhs:v0 ~rhs:vbdy0;
    check_eq ~ctx:ctx ~ty:(Sem.apply vcod D.Dim1) ~lhs:v1 ~rhs:vbdy1

  | _, Tm.Let (t, Tm.B bdy) ->
    let ty' = infer ~ctx ~tm:t in
    let v = Sem.eval_inf (Ctx.env ctx) t in
    check ~ctx:(Ctx.define ~ctx ~tm:v ~ty:ty') ~ty:ty ~tm:bdy

  | _, Tm.Up t ->
    let ty' = infer ~ctx ~tm:t in
    check_subtype ~ctx ~lhs:ty' ~rhs:ty

  | vty, tm ->
    let ty = Sem.quo_nf ctx (D.U `Omega) vty in
    Format.fprintf Format.err_formatter "Failed to check %a <= %a\n" (Tm.Pretty.pp_chk Tm.Pretty.Env.emp) tm (Tm.Pretty.pp_chk Tm.Pretty.Env.emp) ty

and infer ~ctx ~tm =
  match tm with
  | Tm.Var ix ->
    List.nth (Ctx.tys ctx) ix

  | Tm.App (tf, ta) ->
    begin
      match infer ~ctx ~tm:tf with
      | D.Pi (dom, cod) ->
        let v = check_eval ~ctx ~ty:dom ~tm:ta in
        Sem.apply cod v
      | D.Eq (cod, _, _) ->
        let v = check_eval ~ctx ~ty:D.Interval ~tm:ta in
        Sem.apply cod v
      | _ -> failwith "infer/app"
    end

  | Tm.Proj1 t ->
    begin
      match infer ~ctx ~tm:t with
      | D.Sg (dom, _) -> dom
      | _ -> failwith "infer/proj1"
    end

  | Tm.Proj2 t ->
    begin
      match infer ~ctx ~tm:t with
      | D.Sg (dom, cod) ->
        let v = Sem.eval_inf (Ctx.env ctx) (Tm.Proj1 t) in
        Sem.apply cod v
      | _ -> failwith "infer/proj2"
    end

  | Tm.If (Tm.B mot, tb, tt, tf) ->
    let vb = check_eval ~ctx ~ty:D.Bool ~tm:(Tm.Up tb) in
    let ctx', atom = Ctx.add ctx D.Bool in
    check ~ctx:ctx' ~ty:(D.U `Omega) ~tm:mot;
    let rho = Ctx.env ctx in
    let vmott = Sem.eval (D.Tt :: rho) mot in
    check ~ctx ~ty:vmott ~tm:tt;
    let vmotf = Sem.eval (D.Ff :: rho) mot in
    check ~ctx ~ty:vmotf ~tm:tf;
    Sem.eval (vb :: rho) mot

  | Tm.Down (ty, tm) ->
    let vty = check_eval ~ctx ~ty:(D.U `Omega) ~tm:ty in
    check ~ctx ~ty:vty ~tm;
    vty

and check_subtype ~ctx ~lhs ~rhs =
  let _ = Sem.approx_nf ~vr:Sem.Variance.Co ~ctx ~ty:(D.U `Omega) ~lhs ~rhs in
  ()

and check_eq ~ctx ~ty ~lhs ~rhs =
  let _ = Sem.approx_nf ~vr:Sem.Variance.Iso ~ctx ~ty ~lhs ~rhs in
  ()

and check_eval ~ctx ~ty ~tm =
  check ~ctx ~ty ~tm;
  Sem.eval (Ctx.env ctx) tm
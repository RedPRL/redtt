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

  | _ -> failwith ""

and check_eq ~ctx ~ty ~lhs ~rhs =
  let _ = Sem.approx_nf ~vr:Sem.Variance.Iso ~ctx ~ty ~lhs ~rhs in
  ()

and check_eval ~ctx ~ty ~tm = 
  check ~ctx ~ty ~tm;
  Sem.eval (Ctx.env ctx) tm
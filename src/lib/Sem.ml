module D = Val

let rec eval rho t =
  match t with
  | Tm.Pi (dom, cod) -> D.Pi (eval rho dom, D.Clo (cod, rho))
  | Tm.Sg (dom, cod) -> D.Sg (eval rho dom, D.Clo (cod, rho))
  | Tm.Eq (cod, t1, t2) -> D.Eq (D.Clo (cod, rho), eval rho t1, eval rho t2)
  | Tm.U i -> D.U (`Const i)
  | Tm.Unit -> D.Unit
  | Tm.Bool -> D.Bool
  | Tm.Lam bnd -> D.Clo (bnd, rho)
  | Tm.Pair (t1, t2) -> D.Pair (eval rho t1, eval rho t2)
  | Tm.Ax -> D.Ax
  | Tm.Tt -> D.Tt
  | Tm.Ff -> D.Ff
  | Tm.Dim0 -> D.Dim0
  | Tm.Dim1 -> D.Dim1
  | Tm.Up t -> eval_inf rho t

and eval_inf rho t =
  match t with
  | Tm.Var i -> List.nth rho i
  | Tm.App (t1, t2) ->
    let d1 = eval_inf rho t1 in
    let d2 = eval rho t2 in
    apply d1 d2
  | Tm.Proj1 t ->
    proj1 (eval_inf rho t)
  | Tm.Proj2 t ->
    proj2 (eval_inf rho t)
  | Tm.If (bnd, tb, t1, t2) ->
    let mot = D.Clo (bnd, rho) in
    let db = eval_inf rho tb in
    let d1 = eval rho t1 in
    let d2 = eval rho t2 in
    if_ mot db d1 d2
  | Tm.Down (_, tm) ->
    eval rho tm

and apply d1 d2 =
  match d1 with
  | D.Clo (Tm.B t, rho) ->
    eval (d2 :: rho) t
  | D.Up (ty, dne) ->
    begin match ty with
      | D.Pi (dom, cod) ->
        let cod' = apply cod d2 in
        let app = D.App (dne, D.Down (dom, d2)) in
        D.Up (cod', app)
      | D.Eq (cod, p0, p1) ->
        proj_dim (cod, p0, p1) dne d2
      | _ -> failwith "apply/up: unexpected type"
    end
  | _ -> failwith "apply"

and proj_dim (cod, p0, p1) dne dim = 
  let cod' = apply cod dim in
  match dim with 
  | D.Dim0 -> p0 
  | D.Dim1 -> p1
  | _ -> 
    let dim' = D.Down (D.Interval, dim) in
    let app = D.App (dne, dim') in
    D.Up (cod', app)


and proj1 d =
  match d with
  | D.Pair (d1, _d2) -> d1
  | D.Up (ty, dne) ->
    begin match ty with
      | D.Sg (dom, _cod) -> D.Up (dom, D.Proj1 dne)
      | _ -> failwith "proj1/up: unexpected type"
    end
  | _ -> failwith "proj1: not projectible"

and proj2 d =
  match d with
  | D.Pair (_d1, d2) -> d2
  | D.Up (ty, dne) ->
    begin match ty with
      | D.Sg (_dom, cod) ->
        let cod' = apply cod (proj1 d) in
        D.Up (cod', D.Proj2 dne)
      | _ -> failwith "proj2/up: unexpected type"
    end
  | _ -> failwith "proj2: not projectible"

and if_ mot db d1 d2 =
  match db with
  | D.Tt -> d1
  | D.Ff -> d2
  | D.Up (_, dne) ->
    let mot' = apply mot db in
    let dnf1 = D.Down (apply mot D.Tt, d1) in
    let dnf2 = D.Down (apply mot D.Ff, d2) in
    let cond = D.If (mot, dne, dnf1, dnf2) in
    D.Up (mot', cond)
  | _ -> failwith "if: something we can case on"

(* let rec eval_ctx_aux cx =
   match cx with
   | Tm.CNil -> 0, []
   | Tm.CExt (cx, ty) ->
    let (n, rho) = eval_ctx_aux cx in
    let dty = eval rho ty in
    let atom = D.Up (dty, D.Atom n) in
    (n + 1, atom :: rho) *)
(* 
let eval_ctx cx =
  snd (eval_ctx_aux cx) *)

let rec quo_nf (ctx : Ctx.t) dnf =
  let D.Down (dty, d) = dnf in
  match dty, d with

  | D.Pi (dom, cod), _ ->
    let ctx', atom = Ctx.add ctx dom in
    let app = D.Down (apply cod atom, apply d atom) in
    let body = quo_nf ctx' app in
    Tm.Lam (Tm.B body)

  | D.Sg (dom, cod), _ ->
    let d1 = proj1 d in
    let d2 = proj2 d in
    let t1 = quo_nf ctx (D.Down (dom, d1)) in
    let t2 = quo_nf ctx (D.Down (apply cod d1, d2)) in
    Tm.Pair (t1, t2)

  | D.Eq (cod, _d1, _d2), _ ->
    let ctx', atom = Ctx.add ctx D.Interval in
    let app = D.Down (apply cod atom, apply d atom) in
    let body = quo_nf ctx' app in
    Tm.Lam (Tm.B body)

  | D.Unit, _ -> Tm.Ax

  | _, D.U (`Const i) -> Tm.U i
  | _, D.U _ -> failwith "Cannot quote virtual universe U[omega]"

  | univ, D.Pi (dom, cod) ->
    let tdom = quo_nf ctx (D.Down (univ, dom)) in
    let ctx', atom = Ctx.add ctx dom in
    let tcod = quo_nf ctx' (D.Down (univ, apply cod atom)) in
    Tm.Pi (tdom, Tm.B tcod)

  | univ, D.Sg (dom, cod) ->
    let tdom = quo_nf ctx (D.Down (univ, dom)) in
    let ctx', atom = Ctx.add ctx dom in
    let tcod = quo_nf ctx' (D.Down (univ, apply cod atom)) in
    Tm.Sg (tdom, Tm.B tcod)

  | univ, D.Eq (cod, d1, d2) ->
    let ctx', atom = Ctx.add ctx D.Interval in
    let tcod = quo_nf ctx' (D.Down (univ, apply cod atom)) in
    let t1 = quo_nf ctx (D.Down (apply cod D.Dim0, d1)) in
    let t2 = quo_nf ctx (D.Down (apply cod D.Dim1, d2)) in
    Tm.Eq (Tm.B tcod, t1, t2)

  | _, D.Unit -> Tm.Unit
  | _, D.Bool -> Tm.Bool
  | _, D.Tt -> Tm.Tt
  | _, D.Ff -> Tm.Ff
  | _, D.Dim0 -> Tm.Dim0
  | _, D.Dim1 -> Tm.Dim1
  | _, D.Up (_ty, dne) -> let _, t = quo_neu ctx dne in Tm.Up t
  | _, d -> failwith "quo_nf"


and quo_neu ctx dne =
  match dne with 
  | D.Atom lvl -> 
    let ix = Ctx.len ctx - (lvl + 1) in
    let ty = List.nth (Ctx.tys ctx) ix in
    ty, Tm.Var ix

  | D.App (d1, d2) -> 
    begin
      match quo_neu ctx d1 with 
      | D.Pi (vdom, vcod), t1 ->
        let t2 = quo_nf ctx d2 in
        let D.Down (_, d2) = d2 in
        apply vcod d2, Tm.App (t1, t2)
      | D.Eq (vcod, dp0, dp1), t1 -> 
        let t2 = quo_nf ctx d2 in
        let D.Down (_, d2) = d2 in
        apply vcod d2, Tm.App (t1, t2)
      | _ -> failwith "quo_neu/app"
    end

  | D.Proj1 d -> 
    begin
      match quo_neu ctx d with
      | D.Sg (vdom, vcod), t -> 
        vdom, Tm.Proj1 t
      | _ -> failwith "quo_neu/proj1"
    end

  | D.Proj2 d -> 
    begin
      match quo_neu ctx d with
      | D.Sg (vdom, vcod) as vsg, t -> 
        apply vcod (proj1 (D.Up (vsg, d))), Tm.Proj1 t
      | _ -> failwith "quo_neu/proj2"
    end

  | D.If (mot, db, d1, d2) -> 
    let ctx', atom = Ctx.add ~ctx ~ty:D.Bool in 
    let tmot = quo_nf ctx' (D.Down (D.U `Omega, apply mot atom)) in
    let _, tb = quo_neu ctx db in
    let t1 = quo_nf ctx d1 in
    let t2 = quo_nf ctx d2 in
    apply mot (D.Up (D.Bool, db)), Tm.If (Tm.B tmot, tb, t1, t2)

(* let nbe cx ~tm ~ty =
   let n, rho = eval_ctx_aux cx in
   let dty = eval rho ty in
   let dtm = eval rho tm in
   quo_nf n (D.Down (dty, dtm)) *)

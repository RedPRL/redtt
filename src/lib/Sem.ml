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
  | Tm.Let (t1, Tm.B t2) -> eval (eval_inf rho t1 :: rho) t2

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

module Variance = 
struct
  type t = Co | Contra | Iso | None

  let flip v = 
    match v with 
    | Co -> Contra 
    | Contra -> Co
    | Iso -> Iso
    | None -> None
end

module Level = 
struct
  let leq l0 l1 = 
    match l0, l1 with
    | _, `Omega -> true
    | `Const i, `Const j -> i <= j
    | _ -> false

  let as_const l = 
    match l with 
    | `Const i -> i
    | _ -> failwith "Level.as_const"

  let approx v l0 l1 = 
    match v with 
    | Variance.Co ->
      if leq l0 l1 then as_const l1 else failwith "Level.approx"
    | Variance.Contra ->
      if leq l1 l0 then as_const l1 else failwith "Level.approx"
    | Variance.Iso ->
      if l0 = l1 then as_const l0 else failwith "Level.approx"
    | Variance.None -> 
      try as_const l0 with _ -> as_const l1
end

(* Simultaneously check approximation relative to a variance, and quote a normal form *)
let rec approx_nf ~vr ~ctx ~ty:dty ~lhs:d0 ~rhs:d1 =
  match vr with 
  | Variance.None -> 
    (* Don't care about approximation, just want a quote *)
    begin
      try approx_nf ~vr:Variance.Iso ~ctx ~ty:dty ~lhs:d0 ~rhs:d0 with
      | _ -> approx_nf ~vr:Variance.Iso ~ctx ~ty:dty ~lhs:d1 ~rhs:d1
    end

  | _ ->
    match dty, d0, d1 with 
    | D.U _, D.U l0, D.U l1 ->
      let i = Level.approx vr l0 l1 in
      Tm.U i

    | D.U _, D.Unit, D.Unit -> 
      Tm.Unit

    | D.U _, D.Bool, D.Bool -> 
      Tm.Bool

    | D.U _, D.Pi (dom0, cod0), D.Pi (dom1, cod1) -> 
      let tdom = approx_nf (Variance.flip vr) ctx dty dom0 dom1 in
      let ctx', atom = Ctx.add ctx dom0 in
      let tcod = approx_nf vr ctx' dty (apply cod0 atom) (apply cod1 atom) in
      Tm.Pi (tdom, Tm.B tcod)

    | D.U _, D.Sg (dom0, cod0), D.Sg (dom1, cod1) -> 
      let tdom = approx_nf (Variance.flip vr) ctx dty dom0 dom1 in
      let ctx', atom = Ctx.add ctx dom0 in
      let tcod = approx_nf vr ctx' dty (apply cod0 atom) (apply cod1 atom) in
      Tm.Sg (tdom, Tm.B tcod)


    | D.U _, D.Eq (cod0, p00, p01), D.Eq (cod1, p10, p11) ->
      let ctx', atom = Ctx.add ctx D.Interval in
      let tcod = approx_nf vr ctx' dty (apply cod0 atom) (apply cod1 atom) in
      let p0 = approx_nf vr ctx (apply cod0 D.Dim0) p00 p10 in
      let p1 = approx_nf vr ctx (apply cod1 D.Dim1) p01 p11 in
      Tm.Eq (Tm.B tcod, p0, p1)

    | D.Pi (dom, cod), _, _ ->
      let ctx', atom = Ctx.add ctx dom in
      let cod' = apply cod atom in
      let bdy = approx_nf vr ctx' cod' (apply d0 atom) (apply d1 atom) in
      Tm.Lam (Tm.B bdy)

    | D.Sg (dom, cod), _, _ -> 
      let d00 = proj1 d0 in
      let d11 = proj1 d1 in    
      let t0 = approx_nf vr ctx dom d00 d11 in
      let d02 = proj2 d0 in
      let d12 = proj2 d1 in    
      let t1 = approx_nf vr ctx (apply cod d00) d02 d12 in
      Tm.Pair (t0, t1)

    | D.Eq (cod, p0, p1), _, _ ->
      let ctx', atom = Ctx.add ctx D.Interval in
      let cod' = apply cod atom in
      let d0' = apply d0 atom in
      let d1' = apply d1 atom in
      let bdy = approx_nf Variance.None ctx' cod' d0' d1' in
      Tm.Lam (Tm.B bdy)

    | D.Unit, _, _ -> 
      Tm.Ax

    | _, D.Tt, D.Tt -> 
      Tm.Tt

    | _, D.Ff, D.Ff -> 
      Tm.Ff

    | _, D.Dim0, D.Dim0 ->
      Tm.Dim0

    | _, D.Dim1, D.Dim1 ->
      Tm.Dim1

    | _, D.Up (_, dne0), D.Up (_, dne1) ->
      Tm.Up (snd (approx_neu vr ctx dne0 dne1))

    | _ -> failwith "approx_nf: no match"

and approx_neu ~vr ~ctx ~lhs:dne0 ~rhs:dne1 = 
  match dne0, dne1 with 
  | D.Atom lvl0, D.Atom lvl1 -> 
    if lvl0 = lvl1 then 
      let ix = Ctx.len ctx - (lvl0 + 1) in
      let ty = List.nth (Ctx.tys ctx) ix in
      ty, Tm.Var ix
    else 
      failwith "[approx_neu]: atom"

  | D.App (d00, D.Down (_, d01)), D.App (d10, D.Down (_, d11)) -> 
    begin
      match approx_neu vr ctx d00 d10 with 
      | D.Pi (dom, cod), t0 ->
        let t1 = approx_nf vr ctx dom d01 d11 in
        apply cod d01, Tm.App (t0, t1)
      | D.Eq (cod, dp0, dp1), t0 -> 
        let t1 = approx_nf vr ctx D.Interval d01 d11 in
        apply cod d01, Tm.App (t0, t1)
      | _ -> failwith "approx_neu/app"
    end

  | D.Proj1 d0, D.Proj1 d1 -> 
    begin
      match approx_neu vr ctx d0 d1 with 
      | D.Sg (dom, _), t -> 
        dom, Tm.Proj1 t
      | _ -> failwith "approx_neu/proj1"
    end

  | D.Proj2 d0, D.Proj2 d1 -> 
    begin
      match approx_neu vr ctx d0 d1 with 
      | D.Sg (dom, cod) as vsg, t -> 
        apply cod (proj1 (D.Up (vsg, d0))), Tm.Proj2 t
      | _ -> failwith "approx_neu/proj1"
    end

  | D.If (mot0, db0, D.Down (_, dt0), D.Down (_, df0)), D.If (mot1, db1, D.Down (_, dt1), D.Down (_, df1)) ->
    let ctx', atom = Ctx.add ~ctx ~ty:D.Bool in
    let tmot = approx_nf vr ctx' (D.U `Omega) (apply mot0 atom) (apply mot1 atom) in
    let _, tb = approx_neu vr ctx db0 db1 in
    let tt = approx_nf vr ctx (apply mot0 D.Tt) dt0 dt1 in
    let tf = approx_nf vr ctx (apply mot0 D.Ff) df0 df1 in
    apply mot0 (D.Up (D.Bool, db0)), Tm.If (Tm.B tmot, tb, tt, tf)

  | _ -> failwith "approx_neu: no match"


let quo_nf ~ctx ~ty ~tm = 
  approx_nf ~vr:Variance.None ~ctx ~ty ~lhs:tm ~rhs:tm
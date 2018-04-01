type can = [`Can]
type neu = [`Neu]

type 'a bnd = B of 'a

(* TODO: add systems, extension types *)

type _ t = 
  | Idx : int -> can t
  | Lvl : int -> neu t

  | Up : can t * neu t -> can t

  | Pi : clo * bclo -> can t
  | Sg : clo * bclo -> can t
  | Univ : Lvl.t -> can t
  | Interval : can t

  | Lam : bclo -> can t
  | Cons : clo * clo -> can t

  | Coe : can t * can t * can t bnd * can t -> can t

  | App : neu t * can t -> neu t
  | Car : neu t -> neu t
  | Cdr : neu t -> neu t


and env = can t list
and clo = Clo of Thin.t0 * (Tm.chk Tm.t * env * Thin.t0)
and bclo = BClo of Thin.t0 * (Tm.chk Tm.t Tm.vbnd * env * Thin.t0)

(* This should be cheap, because we bottom out at a closure very quickly; the action of
   thinning on a closure is just composition with the closure's outer thinning. *)
let thin : type a. Thin.t0 -> a t -> a t = 
  fun _ -> failwith "TODO: thin"


let clo g (tm, rho, f) = 
  Clo (g, (tm, rho, f))

let bclo g (bnd, rho, f) =
  BClo (g, (bnd, rho, f))

let rec eval : type a. Thin.t0 -> (a Tm.t * env * Thin.t0) -> can t =
  fun g (tm, rho, f) ->
    match Tm.out tm with 
    | Tm.Atom i -> thin g (Idx i)
    | Tm.Var i -> failwith "todo"
    | Tm.Pi (dom, cod) -> Pi (clo g (dom, rho, f), bclo g (cod, rho, f))
    | Tm.Sg (dom, cod) -> Sg (clo g (dom, rho, f), bclo g (cod, rho, f))
    | Tm.Lam bnd -> Lam (bclo g (bnd, rho, f))
    | Tm.Up tm -> eval g (tm, rho, f)
    | Tm.Down {ty; tm} -> eval g (tm, rho, f)
    | Tm.Coe (d0, d1, bnd, tm) ->
      let vd0 = eval g (d0, rho, f) in
      let vd1 = eval g (d1, rho, f) in
      let vty = eval_abnd g (bnd, rho, f) in
      let vtm = eval g (tm, rho, f) in
      Coe (vd0, vd1, vty, vtm)
    | Tm.App (tm0, tm1) ->
      let vfun = eval g (tm0, rho, f) in
      let varg = eval g (tm1, rho, f) in
      apply vfun varg
    | Tm.Car tm -> 
      let v = eval g (tm, rho, f) in
      car v
    | Tm.Cdr tm -> 
      let v = eval g (tm, rho, f) in
      cdr v
    | _ -> failwith "TODO"

and eval_abnd g (Tm.AB tm, rho, f) = 
  B (eval (Thin.keep g) (tm, rho, Thin.skip f))

and apply vfun varg = 
  match vfun with 
  | Lam bclo -> inst_bclo bclo varg
  | Up (Pi (dom, cod), vneu) ->
    let vcod = inst_bclo cod varg in
    reflect vcod (App (vneu, varg))
  | Coe (vd0, vd1, B (Pi (dom, cod)), v) ->
    let vdom = eval_clo dom in
    let vd1' = thin (Thin.skip Thin.id) vd1 in
    let vgen = Idx 0 in
    let vdom' = thin (Thin.keep (Thin.skip Thin.id)) vdom in
    let varg' = thin (Thin.skip Thin.id) varg in
    let vcod = inst_bclo cod (Coe (vd1', vgen, B vdom', varg')) in
    let vapp = apply v (Coe (vd1, vd0, B vdom, varg)) in
    Coe (vd0, vd1, B vcod, vapp)
  | _ -> failwith "apply"


and car v = 
  match v with 
  | Cons (clo, _) -> eval_clo clo
  | Up (Sg (dom, cod), vneu) -> 
    let vdom = eval_clo dom in
    reflect vdom (Car vneu)
  | Coe (vd0, vd1, B (Sg (dom, cod)), v) ->
    let vdom = eval_clo dom in
    let v' = car v in
    Coe (vd0, vd1, B vdom, v')
  | _ -> failwith "car"

and cdr v = 
  match v with 
  | Cons (_, clo) -> eval_clo clo
  | Up (Sg (dom, cod), vneu) ->
    let vcar = car v in
    let vcod = inst_bclo cod vcar in
    reflect vcod (Cdr vneu)
  | Coe (vd0, vd1, B (Sg (dom, cod)), v) -> 
    let vcar = car v in
    let vcdr = cdr v in
    let vdom = eval_clo dom in
    let vd0' = thin (Thin.skip Thin.id) vd0 in
    let vgen = Idx 0 in
    let vdom' = thin (Thin.keep (Thin.skip Thin.id)) vdom in
    let vcar' = thin (Thin.skip Thin.id) vcar in
    let vcoe = Coe (vd0', vgen, B vdom', vcar') in
    let vcod = inst_bclo cod vcoe in
    Coe (vd0, vd1, B vcod, vcdr)
  | _ -> failwith "cdr"

and reflect vty v = failwith "reflect"


and inst_bclo bclo v =
  let BClo (g, (Tm.VB tm, rho, f)) = bclo in
  eval g (tm, v :: rho, f)
and eval_clo : clo -> can t = 
  fun (Clo (g, (tm, rho, f))) -> 
    eval g (tm, rho, f)
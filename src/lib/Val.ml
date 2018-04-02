type can = [`Can]
type neu = [`Neu]

type 'a bnd = B of 'a

(* TODO: add systems, extension types *)

type _ f = 
  | Idx : Thin.t0 -> can f
  | Lvl : int -> neu f

  | Up : can t * neu t -> can f

  | Pi : clo * bclo -> can f
  | Sg : clo * bclo -> can f
  | Univ : Lvl.t -> can f
  | Interval : can f
  | Dim0 : can f
  | Dim1 : can f

  | Lam : bclo -> can f
  | Cons : clo * clo -> can f

  | Coe : can t * can t * can t bnd * can t -> can f

  | App : neu t * can t -> neu f
  | Car : neu t -> neu f
  | Cdr : neu t -> neu f

and 'a t = { thin : Thin.t0; con : 'a f }

and env = can t list
and clo = Clo of Thin.t0 * (Tm.chk Tm.t * env * Thin.t0)
and bclo = BClo of Thin.t0 * (Tm.chk Tm.t Tm.vbnd * env * Thin.t0)

let thin : type a. Thin.t0 -> a t -> a t = 
  fun f node -> 
    { thin = Thin.cmp node.thin f; con = node.con }

let rec thin_f : type a. Thin.t0 -> a f -> a f = 
  fun f v ->
    match v with 
    | Idx ix ->
      failwith "TODO"

    | Lvl i ->
      v

    | Up (vty, vneu) ->
      Up (thin f vty, thin f vneu)

    | Pi (dom, cod) ->
      Pi (thin_clo f dom, thin_bclo f cod)

    | Sg (dom, cod) ->
      Sg (thin_clo f dom, thin_bclo f cod)

    | Univ _ ->
      v

    | Interval ->
      v

    | Dim0 ->
      v

    | Dim1 ->
      v

    | Lam bdy ->
      Lam (thin_bclo f bdy)

    | Cons (clo1, clo2) ->
      Cons (thin_clo f clo1, thin_clo f clo2)

    | Coe (vd0, vd1, bnd, v) ->
      Coe (thin f vd0, thin f vd1, thin_bnd f bnd, thin f v)

    | App (vneu, varg) ->
      App (thin f vneu, thin f varg)

    | Car vneu ->
      Car (thin f vneu)

    | Cdr vneu ->
      Cdr (thin f vneu)

and thin_clo h (Clo (g, (tm, rho, f))) = Clo (Thin.cmp g h, (tm, rho, f))
and thin_bclo h (BClo (g, (tm, rho, f))) = BClo (Thin.cmp g h, (tm, rho, f))
and thin_bnd f (B v) = B (thin (Thin.skip f) v)

let into vf = 
  {thin = Thin.id; con = vf}

let out node = 
  thin_f node.thin node.con


let clo g (tm, rho, f) = 
  Clo (g, (tm, rho, f))

let bclo g (bnd, rho, f) =
  BClo (g, (bnd, rho, f))


let rec eval : type a. Thin.t0 -> (a Tm.t * env * Thin.t0) -> can t =
  fun g (tm, rho, f) ->
    match Tm.out tm with 
    | Tm.Atom i ->
      thin g @@ into @@ (failwith "TODO")

    | Tm.Var i ->
      let v = failwith "todo" in
      thin (Thin.cmp g f) v

    | Tm.Pi (dom, cod) ->
      into @@ Pi (clo g (dom, rho, f), bclo g (cod, rho, f))

    | Tm.Sg (dom, cod) ->
      into @@ Sg (clo g (dom, rho, f), bclo g (cod, rho, f))

    | Tm.Ext _ ->
      failwith "TODO: eval Ext"

    | Tm.Lam bnd ->
      into @@ Lam (bclo g (bnd, rho, f))

    | Tm.Cons (tm1, tm2) -> 
      into @@ Cons (clo g (tm1, rho, f), clo g (tm2, rho, f))

    | Tm.Up tm ->
      eval g (tm, rho, f)

    | Tm.Down {tm; _} ->
      eval g (tm, rho, f)

    | Tm.Coe (d0, d1, bnd, tm) ->
      let vd0 = eval g (d0, rho, f) in
      let vd1 = eval g (d1, rho, f) in
      let vty = eval_abnd g (bnd, rho, f) in
      let vtm = eval g (tm, rho, f) in
      into @@ Coe (vd0, vd1, vty, vtm)

    | Tm.HCom _ ->
      failwith "TODO: eval hcom"

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

    | Tm.Univ lvl ->
      into @@ Univ lvl

    | Tm.Interval -> 
      into Interval

    | Tm.Dim0 ->
      into Dim0

    | Tm.Dim1 ->
      into Dim1


and eval_abnd g (Tm.AB tm, rho, f) = 
  B (eval (Thin.keep g) (tm, rho, Thin.skip f))

and apply vfun varg = 
  match out vfun with 
  | Lam bclo -> inst_bclo bclo varg
  | Up (vty (* Pi (dom, cod) *), vneu) ->
    begin 
      match out vty with 
      | Pi (dom, cod) -> 
        let vcod = inst_bclo cod varg in
        reflect vcod @@ into @@ App (vneu, varg)
      | _ -> failwith "apply/up"
    end
  | Coe (vd0, vd1, B vty, v) ->
    begin
      match out vty with 
      | Pi (dom, cod) ->
        let vdom = eval_clo dom in
        let vd1' = thin (Thin.skip Thin.id) vd1 in
        let vgen = into @@ Idx Thin.id in
        let vdom' = thin (Thin.keep (Thin.skip Thin.id)) vdom in
        let varg' = thin (Thin.skip Thin.id) varg in
        let vcod = inst_bclo cod (into @@ Coe (vd1', vgen, B vdom', varg')) in
        let vapp = apply v (into @@ Coe (vd1, vd0, B vdom, varg)) in
        into @@ Coe (vd0, vd1, B vcod, vapp)
      | _ -> failwith "apply/coe"
    end
  | _ -> failwith "apply"


and car v = 
  match out v with 
  | Cons (clo, _) -> eval_clo clo
  | Up (vty, vneu) -> 
    begin
      match out vty with 
      | Sg (dom, cod) ->
        let vdom = eval_clo dom in
        reflect vdom @@ into @@ Car vneu
      | _ -> failwith "car/up"
    end
  | Coe (vd0, vd1, B vty, v) ->
    begin
      match out vty with 
      | Sg (dom, cod) ->
        let vdom = eval_clo dom in
        let v' = car v in
        into @@ Coe (vd0, vd1, B vdom, v')
      | _ -> failwith "car/coe"
    end
  | _ -> failwith "car"

and cdr v = 
  match out v with 
  | Cons (_, clo) -> eval_clo clo
  | Up (vty, vneu) ->
    begin
      match out vty with 
      | Sg (dom, cod) ->
        let vcar = car v in
        let vcod = inst_bclo cod vcar in
        reflect vcod @@ into @@ Cdr vneu
      | _ -> failwith "cdr/up"
    end
  | Coe (vd0, vd1, B vty, v) -> 
    begin
      match out vty with
      | Sg (dom, cod) ->
        let vcar = car v in
        let vcdr = cdr v in
        let vdom = eval_clo dom in
        let vd0' = thin (Thin.skip Thin.id) vd0 in
        let vgen = into @@ Idx Thin.id in
        let vdom' = thin (Thin.keep (Thin.skip Thin.id)) vdom in
        let vcar' = thin (Thin.skip Thin.id) vcar in
        let vcoe = into @@ Coe (vd0', vgen, B vdom', vcar') in
        let vcod = inst_bclo cod vcoe in
        into @@ Coe (vd0, vd1, B vcod, vcdr)
      | _ -> failwith "cdr/coe"
    end
  | _ -> failwith "cdr"

and reflect vty v = failwith "reflect"

and inst_bclo bclo v =
  let BClo (g, (Tm.VB tm, rho, f)) = bclo in
  eval g (tm, v :: rho, f)

and eval_clo : clo -> can t = 
  fun (Clo (g, (tm, rho, f))) -> 
    eval g (tm, rho, f)
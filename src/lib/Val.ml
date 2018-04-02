type can = [`Can]
type neu = [`Neu]

type 'a bnd = B of 'a

type ('i, 'a) tube = 'i * 'i * 'a
type ('i, 'a) system = ('i, 'a) tube list

type _ f = 
  | Idx : Thin.t0 -> can f
  | Lvl : int -> neu f

  | Up : can t * neu t -> can f

  | Pi : clo * bclo -> can f
  | Sg : clo * bclo -> can f
  | Ext : clo * (can t, clo) system -> can f
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

  | Abort : can f

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
    | Idx g ->
      Idx (Thin.cmp g f)

    | Lvl i ->
      v

    | Up (vty, vneu) ->
      Up (thin f vty, thin f vneu)

    | Pi (dom, cod) ->
      Pi (thin_clo f dom, thin_bclo f cod)

    | Sg (dom, cod) ->
      Sg (thin_clo f dom, thin_bclo f cod)

    | Ext (dom, sys) ->
      Ext (thin_clo f dom, thin_sys f sys)

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

    | Abort ->
      v

and thin_clo h (Clo (g, (tm, rho, f))) = Clo (Thin.cmp g h, (tm, rho, f))
and thin_bclo h (BClo (g, (tm, rho, f))) = BClo (Thin.cmp g h, (tm, rho, f))
and thin_bnd f (B v) = B (thin (Thin.skip f) v)
and thin_sys f sys = List.map (thin_tube f) sys
and thin_tube f (vd0, vd1, clo) = (thin f vd0, thin f vd1, thin_clo f clo)

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
      thin g @@ into @@ Idx i

    | Tm.Var i ->
      let v = Thin.proj i rho in
      thin (Thin.cmp g f) v

    | Tm.Pi (dom, cod) ->
      into @@ Pi (clo g (dom, rho, f), bclo g (cod, rho, f))

    | Tm.Sg (dom, cod) ->
      into @@ Sg (clo g (dom, rho, f), bclo g (cod, rho, f))

    | Tm.Ext (dom, sys) ->
      into @@ Ext (clo g (dom, rho, f), eval_sys g (sys, rho, f))

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

    | Tm.Abort ->
      into Abort


and eval_sys g (sys, rho, f) = 
  List.map (fun tb -> eval_tube g (tb, rho, f)) sys

and eval_tube g ((t0, t1, tm), rho, f) =
  let vd0 = eval g (t0, rho, f) in
  let vd1 = eval g (t1, rho, f) in
  let bdy =
    begin 
      match out vd0, out vd1 with 
      | Dim0, Dim1 -> clo Thin.id (Tm.into Tm.Abort, [], Thin.id)
      | Dim1, Dim0 -> clo Thin.id (Tm.into Tm.Abort, [], Thin.id)
      | _ -> clo g (tm, rho, f)
    end
  in
  (vd0, vd1, bdy)

and eval_abnd g (Tm.AB tm, rho, f) = 
  B (eval (Thin.keep g) (tm, rho, Thin.skip f))

and apply vfun varg = 
  match out vfun with 
  | Lam bclo -> inst_bclo bclo varg
  | Up (vty, vneu) ->
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

and reflect vty vneu =
  match out vty with
  | Ext (dom, sys) ->
    reflect_ext dom sys vneu
  | _ -> into @@ Up (vty, vneu)

and reflect_ext dom sys vneu = 
  match sys with 
  | [] -> reflect (eval_clo dom) vneu
  | (vd0, vd1, clo) :: sys ->
    if dim_eq vd0 vd1 then 
      eval_clo clo
    else
      reflect_ext dom sys vneu

and dim_eq vd0 vd1 =
  match out vd0, out vd1 with
  | Dim0, Dim0 -> true
  | Dim1, Dim1 -> true
  | Idx f, Idx g -> Thin.Ix.to_ix f = Thin.Ix.to_ix g
  | Up (_, vnd0), Up (_, vnd1) ->
    dim_eq_neu vnd0 vnd1
  | _ -> false

(* The only reason this makes sense is that the neutral form of dimensions
   can only be variables or atoms. This does *not* work if we allow dimensions
   to appear in sigma types, or on the rhs of pi types, etc. *)
and dim_eq_neu vnd0 vnd1 = 
  match out vnd0, out vnd1 with 
  | Lvl i, Lvl j -> i = j
  | _ -> false



and inst_bclo bclo v =
  let BClo (g, (Tm.VB tm, rho, f)) = bclo in
  eval g (tm, v :: rho, f)

and eval_clo : clo -> can t = 
  fun (Clo (g, (tm, rho, f))) -> 
    eval g (tm, rho, f)
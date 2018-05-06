module R = Restriction
module P = Permutation
module D = DimVal

type atom = Symbol.t

module Dim :
sig
  type t

  val make : D.t -> t
  val compare : t -> t -> D.compare

  val perm : P.t -> t -> t
  val restrict : R.t -> t -> t

  val equate_with : t -> t -> R.t
end =
struct
  type t = {r : D.t; phi : R.t}

  let make r =
    {r; phi = R.emp}

  let compare c d =
    let phi = R.union c.phi d.phi in
    R.compare c.r d.r phi

  let perm pi c =
    {phi = R.perm pi c.phi;
     r = P.read c.r pi}

  let restrict phi c =
    {c with phi = R.union phi c.phi}

  let equate_with c d =
    R.union (R.equate c.r d.r) @@
    R.union c.phi d.phi
end

module Star :
sig
  type t
  type 'a m = [`Ok of 'a | `Same of Dim.t * Dim.t]

  val make : Dim.t -> Dim.t -> t m
  val unleash : t -> Dim.t * Dim.t
  val perm : P.t -> t -> t
  val restrict : R.t -> t -> t m
end =
struct
  type t = Dim.t * Dim.t
  type 'a m = [`Ok of 'a | `Same of t]

  let make c d =
    match Dim.compare c d with
    | D.Same ->
      `Same (c, d)
    | _ ->
      `Ok (c, d)

  let unleash p = p

  let perm pi (c, d) =
    Dim.perm pi c, Dim.perm pi d

  let restrict phi (c, d) =
    make (Dim.restrict phi c) (Dim.restrict phi d)
end

module Gen :
sig
  type t
  type 'a m = [`Ok of 'a | `Const of [`Dim0 | `Dim1]]
  val make : Dim.t -> t m
  val unleash : t -> Dim.t
  val perm : P.t -> t -> t
  val restrict : R.t -> t -> t m
end =
struct
  type t = Dim.t
  type 'a m = [`Ok of 'a | `Const of [`Dim0 | `Dim1]]

  let make c =
    match Dim.compare c (Dim.make D.Dim0) with
    | D.Same -> `Const `Dim0
    | _ ->
      match Dim.compare c (Dim.make D.Dim1) with
      | D.Same -> `Const `Dim1
      | _ -> `Ok c

  let unleash c = c

  let perm pi c =
    Dim.perm pi c

  let restrict phi c =
    make @@ Dim.restrict phi c
end

type can = [`Can]
type neu = [`Neu]

type frame =
  | Restrict of R.t
  | Perm of P.t

let enqueue f fs =
  match f, fs with
  | Restrict phi, Restrict phi' :: fs ->
    Restrict (R.union phi phi') :: fs
  | Perm pi, Perm pi' :: fs ->
    Perm (P.cmp pi pi') :: fs
  | _ ->
    f::fs


type _ con =
  | Loop : Gen.t -> can con
  | Base : can con
  | Coe : {dir : Star.t; abs : abs; el : can value} -> can con
  | HCom : {dir : Star.t; ty : can value; cap : can value; sys : comp_sys} -> can con
  | Pi : {dom : can value; cod : clo} -> can con
  | Lam : clo -> can con
  | Bool : can con

and 'a with_env = {tm : 'a; rho : env}
and (_, 'a) face =
  | False : Star.t -> ('x, 'a) face
  | True : Dim.t * Dim.t * 'a -> ([`Any], 'a) face
  | Indet : Star.t * 'a -> ('x, 'a) face

and cfg = Tm.chk Tm.t with_env node
and clo = Tm.chk Tm.t Tm.bnd with_env node
and env_el = Val of can value | Atom of atom
and env = env_el list

and comp_sys = ([`Rigid], abs) face list
and ext_sys = ([`Any], can value) face list
and box_sys = ([`Rigid], can value) face list
and cap_sys = ([`Rigid], can value) face list

and abs = {atom : atom; node : can value}
and 'a node = {inner : 'a; queue : frame list}
and 'a value = 'a con node ref


type 'a step = [`Ret of 'a con | `Step of 'a value]

let ret v = `Ret v
let step v = `Step v

module Val =
struct
  let into : type a. a con -> a value =
    fun inner ->
      ref @@ {inner; queue = []}

  let from_step step =
    match step with
    | `Ret con -> into con
    | `Step t -> t

  let perm : type a. P.t -> a value -> a value =
    fun pi node ->
      ref @@ {!node with queue = enqueue (Perm pi) !node.queue}

  let restrict : type a. R.t -> a value -> a value =
    fun phi node ->
      ref @@ {!node with queue = enqueue (Restrict phi) !node.queue}
end

module type Sort =
sig
  type t
  type 'a m
  val restrict : R.t -> t -> t m
  val perm : P.t -> t -> t
end

module CanVal : Sort with type t = can value with type 'a m = 'a =
struct
  include Val
  type 'a m = 'a
  type t = can value
end


module Abs :
sig
  include Sort with type t = abs with type 'a m = 'a
  val bind : atom -> can value -> t
  val unleash : t -> atom * can value
end =
struct
  type 'a m = 'a
  type t = abs

  let unleash abs =
    let x = Symbol.fresh () in
    x, Val.perm (P.swap x abs.atom) abs.node

  let perm pi abs =
    {atom = P.lookup abs.atom pi;
     node = Val.perm pi abs.node}

  let bind atom node =
    {atom; node}

  let restrict phi abs =
    let x, node = unleash abs in
    bind x @@ Val.restrict phi node
end


module Face (X : Sort with type 'a m = 'a) :
sig
  type 'x t = ('x, X.t) face

  val restrict : R.t -> 'x t -> [`Any] t
  val perm : P.t -> 'x t -> 'x t
end =
struct
  type 'x t = ('x, X.t) face

  let restrict : type x. R.t -> x t -> _ t =
    fun phi face ->
      match face with
      | True (c, d, t) ->
        True (Dim.restrict phi c, Dim.restrict phi d, X.restrict phi t)
      | False p ->
        False p
      | Indet (p, t) ->
        let t' = X.restrict phi t in
        match Star.restrict phi p with
        | `Ok p' ->
          Indet (p', t')
        | `Same (c, d) ->
          True (c, d, t')

  let perm : type x. P.t -> x t -> x t =
    fun pi face ->
      match face with
      | True (c, d, t) ->
        True (Dim.perm pi c, Dim.perm pi d, X.perm pi t)
      | False p ->
        False (Star.perm pi p)
      | Indet (p, t) ->
        Indet (Star.perm pi p, X.perm pi t)
end

module ValFace = Face (CanVal)
module AbsFace = Face (Abs)


module Clo : Sort with type t = clo with type 'a m = 'a =
struct
  type t = clo
  type 'a m = 'a

  let perm pi clo =
    {clo with queue = enqueue (Perm pi) clo.queue}

  let restrict phi clo =
    {clo with queue = enqueue (Restrict phi) clo.queue}
end

module CompSys :
sig
  include Sort
    with type t = comp_sys
    with type 'a m = [`Ok of comp_sys | `Proj of abs]
end =
struct
  type t = comp_sys
  type 'a m = [`Ok of comp_sys | `Proj of abs]

  exception Proj of abs

  let rec restrict_aux phi sys =
    match sys with
    | [] -> []
    | face :: sys ->
      match AbsFace.restrict phi face with
      | True (_, _, abs) ->
        raise @@ Proj abs
      | False p ->
        False p :: restrict_aux phi sys
      | Indet (p, t) ->
        Indet (p, t) :: restrict_aux phi sys

  let restrict phi sys =
    try `Ok (restrict_aux phi sys)
    with
    | Proj abs ->
      `Proj abs

  let perm pi =
    List.map (AbsFace.perm pi)
end


module Con =
struct
  let perm : type a. P.t -> a con -> a con =
    fun pi con ->
      match con with
      | Loop x ->
        Loop (Gen.perm pi x)
      | Base ->
        con
      | Coe info ->
        let dir = Star.perm pi info.dir in
        let abs = Abs.perm pi info.abs in
        let el = Val.perm pi info.el in
        Coe {dir; abs; el}
      | HCom info ->
        let dir = Star.perm pi info.dir in
        let ty = Val.perm pi info.ty in
        let cap = Val.perm pi info.ty in
        let sys = List.map (AbsFace.perm pi) info.sys in
        HCom {dir; ty; cap; sys}
      | Pi info ->
        let dom = Val.perm pi info.dom in
        let cod = Clo.perm pi info.cod in
        Pi {dom; cod}
      | Bool ->
        con
      | Lam clo ->
        Lam (Clo.perm pi clo)

  let rec restrict : type a. R.t -> a con -> a step =
    fun phi con ->
      match con with
      | Loop x ->
        ret @@
        begin
          match Gen.restrict phi x with
          | `Ok y -> Loop y
          | `Const _ -> Base
        end

      | Base ->
        ret con

      | Coe info ->
        make_coe
          (Star.restrict phi info.dir)
          (lazy begin Abs.restrict phi info.abs end)
          (lazy begin Val.restrict phi info.el end)

      | HCom info ->
        failwith ""

      | Bool ->
        ret con

      | Lam clo ->
        ret @@ Lam (Clo.restrict phi clo)

      | Pi info ->
        let dom = Val.restrict phi info.dom in
        let cod = Clo.restrict phi info.cod in
        ret @@ Pi {dom; cod}

  and make_coe mdir abs el : can step =
    match mdir with
    | `Ok dir ->
      rigid_coe dir (Lazy.force abs) (Lazy.force el)
    | `Same _ ->
      step @@ Lazy.force el

  and make_hcom mdir ty cap msys : can step =
    match mdir with
    | `Ok dir ->
      begin
        match Lazy.force msys with
        | `Ok sys ->
          rigid_hcom dir (Lazy.force ty) (Lazy.force cap) sys
        | `Proj abs ->
          let _, r' = Star.unleash dir in
          let x, el = Abs.unleash abs in
          step @@ Val.restrict (Dim.equate_with r' (Dim.make @@ D.Named x)) el
      end
    | `Same ->
      step @@ Lazy.force cap

  and rigid_coe dir abs el : can step =
    let _, ty = Abs.unleash abs in
    match unleash ty with
    | Pi _ ->
      ret @@ Coe {dir; abs; el}
    | Bool ->
      step el
    | _ -> failwith ""

  and rigid_hcom dir ty cap sys : can step =
    failwith ""

  and unleash : type a. a value -> a con =
    fun node ->
      let inner = eval_queue !node.queue !node.inner in
      node := {inner; queue = []};
      inner

  and eval_stack : type a. frame list -> a con -> a con =
    fun fs con ->
      match fs with
      | [] -> con
      | f :: fs ->
        eval_stack fs @@
        match f with
        | Restrict phi ->
          begin
            match restrict phi con with
            | `Ret con -> con
            | `Step node -> unleash node
          end
        | Perm pi -> perm pi con

  and eval_queue : type a. frame list -> a con -> a con =
    fun fs con ->
      eval_stack (List.rev fs) con

end

let rec eval_queue_dim fs c =
  eval_stack_dim (List.rev fs) c

and eval_stack_dim fs c =
  match fs with
  | [] -> c
  | f :: fs ->
    eval_stack_dim fs @@
    match f with
    | Restrict phi ->
      Dim.restrict phi c
    | Perm pi ->
      Dim.perm pi c


let eval_dim (cfg : cfg) : Dim.t =
  match Tm.out cfg.inner.tm with
  | Tm.Dim0 ->
    Dim.make D.Dim0
  | Tm.Dim1 ->
    Dim.make D.Dim1
  | Tm.Var i ->
    begin
      match List.nth cfg.inner.rho i with
      | Atom x ->
        eval_queue_dim cfg.queue @@
        Dim.make (D.Named x)
      | _ ->
        failwith "eval_dim: expected atom in environment"
    end
  | _ ->
    failwith "eval_dim"

let set_tm tm cfg =
  {cfg with inner = {cfg.inner with tm}}

let rec eval (cfg : cfg) : can value =
  match Tm.out cfg.inner.tm with
  | Tm.Lam bnd ->
    Val.into @@ Lam (set_tm bnd cfg)

  | Tm.Coe info ->
    Val.from_step @@
    let r = eval_dim @@ set_tm info.dim0 cfg in
    let r' = eval_dim @@ set_tm info.dim1 cfg in
    let dir = Star.make r r' in
    let abs = lazy (eval_abs info.ty cfg) in
    let el = lazy (eval @@ set_tm info.tm cfg) in
    Con.make_coe dir abs el

  | _ ->
    failwith ""

and eval_abs bnd cfg =
  let Tm.B (_, tm) = bnd in
  let x = Symbol.fresh () in
  let rho = Atom x :: cfg.inner.rho in
  Abs.bind x @@ eval {cfg with inner = {tm; rho}}

and apply vfun varg =
  match Con.unleash vfun with
  | Lam clo ->
    inst_clo clo varg

  | _ ->
    failwith ""


and inst_clo clo varg =
  let Tm.B (_, tm) = clo.inner.tm in
  eval {clo with inner = {tm; rho = Val varg :: clo.inner.rho}}


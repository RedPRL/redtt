type atom = Symbol.t

module D :
sig
  type t
  val dim0 : t
  val dim1 : t
  val named : atom -> t

  type compare =
    | Same
    | Apart
    | Indeterminate

  val compare : t -> t -> compare


  type action
  val subst : t -> atom -> action
  val equate : t -> t -> action
  val swap : atom -> atom -> action
  val cmp : action -> action -> action
  val idn : action

  val act : action -> t -> t
end =
struct
  type t =
    | Dim0
    | Dim1
    | Atom of {atom : atom; history : atom list}

  let dim0 = Dim0
  let dim1 = Dim1
  let named x = Atom {atom = x; history = []}

  type action =
    | Subst of t * atom
    | Swap of atom * atom
    | Diag of atom * (atom * atom)
    | Cmp of action * action
    | Id

  let subst r x = Subst (r, x)

  let equate r r' =
    match r, r' with
    | Dim0, Dim0 ->
      Id
    | Dim1, Dim1 ->
      Id
    | Dim0, Atom atm ->
      subst Dim0 atm.atom
    | Dim1, Atom atm ->
      subst Dim1 atm.atom
    | Atom atm, Dim0 ->
      subst Dim0 atm.atom
    | Atom atm, Dim1 ->
      subst Dim1 atm.atom
    | Atom atm0, Atom atm1 ->
      let z = Symbol.fresh () in
      Diag (z, (atm0.atom, atm1.atom))
    | _ ->
      failwith "Inconsistent equation"

  let cmp sigma1 sigma0 =
    Cmp (sigma1, sigma0)

  let idn = Id

  let swap x y =
    Swap (x, y)

  type compare =
    | Same
    | Apart
    | Indeterminate

  let compare r r' =
    match r, r' with
    | Dim0, Dim0 -> Same
    | Dim1, Dim1 -> Same
    | Dim0, Dim1 -> Apart
    | Dim1, Dim0 -> Apart
    | Atom atm0, Atom atm1 ->
      if atm0.atom = atm1.atom then
        Same
      else
        Indeterminate
    | _ -> Indeterminate

  let atom_swap (x, y) z =
    if x = z then y else if y = z then x else z

  let rec act sigma r =
    match r, sigma with
    | (Dim0 | Dim1), _ -> r
    | _, Id -> r
    | _, Cmp (sigma1, sigma0) ->
      act sigma1 @@ act sigma0 r
    | Atom atm, Subst (r', x) ->
      if atm.atom = x then r' else r
    | Atom atm, Diag (z, (x, y)) ->
      if atm.atom = x then
        Atom {atom = z; history = x :: atm.history}
      else if atm.atom = y then
        Atom {atom = z; history = y :: atm.history}
      else
        r
    | Atom atm, Swap (x, y) ->
      Atom
        {atom = atom_swap (x, y) atm.atom;
         history = List.map (atom_swap (x, y)) atm.history}
end

module Star :
sig
  type t
  type 'a m = [`Ok of 'a | `Same of D.t * D.t]

  val make : D.t -> D.t -> t m
  val unleash : t -> D.t * D.t
  val act : D.action -> t -> t m
end =
struct
  type t = D.t * D.t
  type 'a m = [`Ok of 'a | `Same of t]

  let make c d =
    match D.compare c d with
    | D.Same ->
      `Same (c, d)
    | _ ->
      `Ok (c, d)

  let unleash p = p

  let act phi (r, r') =
    make (D.act phi r) (D.act phi r')
end


module Gen :
sig
  type t
  type 'a m = [`Ok of 'a | `Const of [`Dim0 | `Dim1]]
  val make : D.t -> t m
  val unleash : t -> D.t
  val act : D.action -> t -> t m
end =
struct
  type t = D.t
  type 'a m = [`Ok of 'a | `Const of [`Dim0 | `Dim1]]

  let make c =
    match D.compare c D.dim0 with
    | D.Same -> `Const `Dim0
    | _ ->
      match D.compare c D.dim0 with
      | D.Same -> `Const `Dim1
      | _ -> `Ok c

  let unleash c = c

  let act phi r =
    make @@ D.act phi r
end

type can = [`Can]
type neu = [`Neu]

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
  | True : D.t * D.t * 'a -> ([`Any], 'a) face
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
and 'a node = {inner : 'a; action : D.action}
and 'a value = 'a con node ref
type 'a step = [`Ret of 'a con | `Step of 'a value]

let ret v = `Ret v
let step v = `Step v

module type Sort =
sig
  type t
  type 'a m
  val act : D.action -> t -> t m
end

module Val =
struct
  let into : type a. a con -> a value =
    fun inner ->
      ref @@ {inner; action = D.idn}

  let from_step step =
    match step with
    | `Ret con -> into con
    | `Step t -> t

  let act : type a. D.action -> a value -> a value =
    fun phi node ->
      ref @@ {!node with action = D.cmp phi !node.action}
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
    x, Val.act (D.swap x abs.atom) abs.node

  let bind atom node =
    {atom; node}

  let act phi abs =
    let x, node = unleash abs in
    bind x @@ Val.act phi node
end

module Face (X : Sort with type 'a m = 'a) :
sig
  type 'x t = ('x, X.t) face
  val act : D.action -> 'x t -> [`Any] t
end =
struct
  type 'x t = ('x, X.t) face

  let act : type x. D.action -> x t -> _ t =
    fun phi face ->
      match face with
      | True (c, d, t) ->
        True (D.act phi c, D.act phi d, X.act phi t)
      | False p ->
        False p
      | Indet (p, t) ->
        let t' = X.act phi t in
        match Star.act phi p with
        | `Ok p' ->
          Indet (p', t')
        | `Same (c, d) ->
          True (c, d, t')
end

module ValFace = Face (CanVal)
module AbsFace = Face (Abs)

module Clo : Sort with type t = clo with type 'a m = 'a =
struct
  type t = clo
  type 'a m = 'a

  let act phi clo =
    {clo with action = D.cmp phi clo.action}
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

  let rec act_aux phi sys =
    match sys with
    | [] -> []
    | face :: sys ->
      match AbsFace.act phi face with
      | True (_, _, abs) ->
        raise @@ Proj abs
      | False p ->
        False p :: act_aux phi sys
      | Indet (p, t) ->
        Indet (p, t) :: act_aux phi sys

  let act phi sys =
    try `Ok (act_aux phi sys)
    with
    | Proj abs ->
      `Proj abs
end


module Con =
struct
  let rec act : type a. D.action -> a con -> a step =
    fun phi con ->
      match con with
      | Loop x ->
        ret @@
        begin
          match Gen.act phi x with
          | `Ok y -> Loop y
          | `Const _ -> Base
        end

      | Base ->
        ret con

      | _ -> failwith ""

  and unleash : type a. a value -> a con =
    fun node ->
      match act !node.action !node.inner with
      | `Ret con ->
        node := {inner = con; action = D.idn};
        con
      | `Step t ->
        let con = unleash t in
        node := {inner = con; action = D.idn};
        con

  (*
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
      eval_stack (List.rev fs) con *)

end

(*
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


*)

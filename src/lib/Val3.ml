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

  (* The [Atom] constructor is the only weird case. It is implemented this way in order to
     support diagonal equations, which we treat as different from the substitution of one
     dimension for an atom. In the case of a diagonal x=y, we generate a fresh atom 'z',
     and then replace both and y with z; except, using the [history] field, we remember that
     each one used to be x or y.

     When comparing generic dimensions, only the [atom] field is considered; but using the history,
     we can reconstruct the 'real' name of the dimension, which is crucial for quotation. *)

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


(* Even now, one potential issue with this algorithm is that I think substitution action
   still isn't a priori functorial for HCom. That is, suppose we first apply a substitution that makes
   [r /= r'] but [|= xi_k]; this causes a face to be projected; then we do another substitution
   that made [r = r'].  This is not the same as composing the substitutions and then running them,
   because that would cause the cap to be projected.

   However, these will be the same in the definitional equality if the term started off as well-typed.
   So that seems like it is OK; the disadvantage is that there is no sense in which we can regard
   ourselves as having defined a priori a presheaf of values---however, it will, for each type, induce a
   presheaf of values.

   As a side-remark, I was thinking that for the untyped case, it seems like one could implement a version
   where substitution really did commute using a control effect: once we receive a substitution that causes the
   cap to become available, we actually JUMP back to where we started and re-run everything against the cap
   instead of the projected tube. Might be worth figuring out some day.
*)
type _ con =
  | Loop : Gen.t -> can con
  | Base : can con
  | Coe : {dir : Star.t; abs : abs; el : can value} -> can con
  | HCom : {dir : Star.t; ty : can value; cap : can value; sys : comp_sys} -> can con
  | Pi : {dom : can value; cod : clo} -> can con
  | Lam : clo -> can con
  | Bool : can con

and (_, 'a) face =
  | False : Star.t -> ('x, 'a) face
  | True : D.t * D.t * 'a -> ([`Any], 'a) face
  | Indet : Star.t * 'a -> ('x, 'a) face

and 'a with_env = {tm : 'a; rho : env}
and cfg = Tm.chk Tm.t with_env node
and clo = Tm.chk Tm.t Tm.bnd with_env node
and env_el = Val of can value | Atom of atom
and env = env_el list

and rigid_abs_face = ([`Rigid], abs) face
and val_face = ([`Any], can value) face
and rigid_val_face = ([`Rigid], can value) face

and comp_sys = rigid_abs_face list
and ext_sys = val_face list
and box_sys = rigid_val_face list
and cap_sys = rigid_abs_face list

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

  (* FYI: It may not be necessary to freshen here, depending on how substitution is implemented. *)
  let bind atom node =
    let x = Symbol.fresh () in
    {atom = x; node = Val.act (D.swap x atom) node}

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

      | Coe info ->
        make_coe
          (Star.act phi info.dir)
          (lazy begin Abs.act phi info.abs end)
          (lazy begin Val.act phi info.el end)

      | HCom info ->
        make_hcom
          (Star.act phi info.dir)
          (lazy begin Val.act phi info.ty end)
          (lazy begin Val.act phi info.cap end)
          (lazy begin CompSys.act phi info.sys end)

      | Bool ->
        ret con

      | Lam clo ->
        ret @@ Lam (Clo.act phi clo)

      | Pi info ->
        let dom = Val.act phi info.dom in
        let cod = Clo.act phi info.cod in
        ret @@ Pi {dom; cod}


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
          step @@ Val.act (D.subst r' x) el
      end
    | `Same _ ->
      step @@ Lazy.force cap

  and rigid_coe dir abs el : can step =
    let _, ty = Abs.unleash abs in
    match unleash ty with
    | Pi _ ->
      ret @@ Coe {dir; abs; el}
    | Bool ->
      step el
    | _ ->
      failwith "TODO"

  and rigid_hcom dir ty cap sys : can step =
    match unleash ty with
    | Pi _ ->
      ret @@ HCom {dir; ty; cap; sys}
    | Bool ->
      step cap
    | _ ->
      failwith "TODO"

end

let eval_dim (cfg : cfg) : D.t =
  match Tm.out cfg.inner.tm with
  | Tm.Dim0 ->
    D.dim0
  | Tm.Dim1 ->
    D.dim1
  | Tm.Var i ->
    begin
      match List.nth cfg.inner.rho i with
      | Atom x ->
        D.act cfg.action @@ D.named x
      | _ ->
        failwith "eval_dim: expected atom in environment"
    end
  | _ ->
    failwith "eval_dim"

let set_tm tm cfg =
  {cfg with inner = {cfg.inner with tm}}

exception Proj of abs

let rec eval (cfg : cfg) : can value =
  match Tm.out cfg.inner.tm with
  | Tm.Lam bnd ->
    Val.into @@ Lam (set_tm bnd cfg)

  | Tm.Coe info ->
    Val.from_step @@
    let r = eval_dim @@ set_tm info.dim0 cfg in
    let r' = eval_dim @@ set_tm info.dim1 cfg in
    let dir = Star.make r r' in
    let abs = lazy (eval_abs @@ set_tm info.ty cfg) in
    let el = lazy (eval @@ set_tm info.tm cfg) in
    Con.make_coe dir abs el

  | Tm.HCom info ->
    Val.from_step @@
    let r = eval_dim @@ set_tm info.dim0 cfg in
    let r' = eval_dim @@ set_tm info.dim1 cfg in
    let dir = Star.make r r' in
    let ty = lazy (eval @@ set_tm info.ty cfg) in
    let cap = lazy (eval @@ set_tm info.cap cfg) in
    let sys = lazy (eval_abs_sys @@ set_tm info.sys cfg) in
    Con.make_hcom dir ty cap sys

  | Tm.FunApp (t0, t1) ->
    let v0 = eval @@ set_tm t0 cfg in
    let v1 = eval @@ set_tm t1 cfg in
    apply v0 v1

  | _ ->
    failwith ""

and eval_abs_face cfg =
  let tr, tr', obnd = cfg.inner.tm in
  let r = eval_dim @@ set_tm tr cfg in
  let r' = eval_dim @@ set_tm tr' cfg in
  match Star.make r r' with
  | `Ok xi ->
    begin
      match D.compare r r' with
      | D.Apart ->
        False xi
      | _ ->
        let bnd = Option.get_exn obnd in
        let abs =
          lazy begin
            eval_abs
              {inner = {cfg.inner with tm = bnd};
               action = D.cmp (D.equate r r') cfg.action}
          end
        in
        Indet (xi, abs)
    end
  | `Same _ ->
    let bnd = Option.get_exn obnd in
    let abs = lazy begin eval_abs @@ set_tm bnd cfg end in
    True (r, r', abs)

and force_rigid_face face =
  match face with
  | True (_, _, abs) ->
    raise @@ Proj (Lazy.force abs)
  | False xi ->
    False xi
  | Indet (xi, abs) ->
    Indet (xi, Lazy.force abs)

and eval_abs_sys cfg =
  try
    let sys =
      List.map
        (fun x -> force_rigid_face @@ eval_abs_face @@ set_tm x cfg)
        cfg.inner.tm
    in `Ok sys
  with
  | Proj abs ->
    `Proj abs

and eval_abs cfg =
  let Tm.B (_, tm) = cfg.inner.tm in
  let x = Symbol.fresh () in
  let rho = Atom x :: cfg.inner.rho in
  Abs.bind x @@ eval {cfg with inner = {tm; rho}}

and out_pi v =
  match Con.unleash v with
  | Pi {dom; cod} -> dom, cod
  | _ -> failwith "out_pi"

and apply vfun varg =
  match Con.unleash vfun with
  | Lam clo ->
    inst_clo clo varg

  | Coe info ->
    Val.from_step @@
    let r, r' = Star.unleash info.dir in
    let x, tyx = Abs.unleash info.abs in
    let domx, codx = out_pi tyx in
    let abs =
      Abs.bind x @@
      inst_clo codx @@
      Val.from_step @@
      Con.make_coe
        (Star.make r' (D.named x))
        (lazy begin Abs.bind x domx end)
        (lazy varg)
    in
    let el =
      apply info.el @@
      Val.from_step @@
      Con.make_coe
        (Star.make r' r)
        (lazy begin Abs.bind x domx end)
        (lazy varg)
    in
    Con.rigid_coe info.dir abs el

  | _ ->
    failwith ""


and inst_clo clo varg =
  let Tm.B (_, tm) = clo.inner.tm in
  eval {clo with inner = {tm; rho = Val varg :: clo.inner.rho}}

type atom = Symbol.t
module D = Dim
module Star = DimStar
module Gen = DimGeneric

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
  | Pi : {dom : can value; cod : clo} -> can con
  | Sg : {dom : can value; cod : clo} -> can con
  | Ext : (can value * ext_sys) Abstraction.abs -> can con
  | Coe : {dir : Star.t; abs : abs; el : can value} -> can con
  | HCom : {dir : Star.t; ty : can value; cap : can value; sys : comp_sys} -> can con
  | Lam : clo -> can con
  | Bool : can con

and ('x, 'a) face = ('x, 'a) Face.face

and 'a with_env = {tm : 'a; rho : env}
and cfg = Tm.chk Tm.t with_env node
and clo = Tm.chk Tm.t Tm.bnd with_env node
and env_el = Val of can value | Atom of atom
and env = env_el list

and abs = can value Abstraction.abs
and rigid_abs_face = ([`Rigid], abs) face
and val_face = ([`Any], can value) face
and rigid_val_face = ([`Rigid], can value) face

and comp_sys = rigid_abs_face list
and ext_sys = val_face list
and box_sys = rigid_val_face list
and cap_sys = rigid_abs_face list

and 'a node = {inner : 'a; action : D.action}
and 'a value = 'a con node ref
type 'a step = [`Ret of 'a con | `Step of 'a value]

let ret v = `Ret v
let step v = `Step v

module type Sort = Sort.S

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

module Abs = Abstraction.M (CanVal)

module ValFace = Face.M (CanVal)
module AbsFace = Face.M (Abs)

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

  let rec act_aux phi (sys : t) =
    match sys with
    | [] -> []
    | face :: sys ->
      match AbsFace.act phi face with
      | Face.True (_, _, abs) ->
        raise @@ Proj abs
      | Face.False p ->
        Face.False p :: act_aux phi sys
      | Face.Indet (p, t) ->
        Face.Indet (p, t) :: act_aux phi sys

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
      | Pi info ->
        let dom = Val.act phi info.dom in
        let cod = Clo.act phi info.cod in
        ret @@ Pi {dom; cod}

      | Sg info ->
        let dom = Val.act phi info.dom in
        let cod = Clo.act phi info.cod in
        ret @@ Sg {dom; cod}

      | Ext _abs ->
        failwith "TODO"

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
  | Tm.Pi (dom, cod) ->
    let dom = eval @@ set_tm dom cfg in
    let cod = set_tm cod cfg in
    Val.into @@ Pi {dom; cod}

  | Tm.Sg (dom, cod) ->
    let dom = eval @@ set_tm dom cfg in
    let cod = set_tm cod cfg in
    Val.into @@ Sg {dom; cod}

  | Tm.Ext (Tm.B (_, (_cod, _sys))) ->
    failwith "TODO"

  | Tm.Lam bnd ->
    Val.into @@ Lam (set_tm bnd cfg)

  | Tm.Coe info ->
    Val.from_step @@
    let r = eval_dim @@ set_tm info.r cfg in
    let r' = eval_dim @@ set_tm info.r' cfg in
    let dir = Star.make r r' in
    let abs = lazy (eval_abs @@ set_tm info.ty cfg) in
    let el = lazy (eval @@ set_tm info.tm cfg) in
    Con.make_coe dir abs el

  | Tm.HCom info ->
    Val.from_step @@
    let r = eval_dim @@ set_tm info.r cfg in
    let r' = eval_dim @@ set_tm info.r' cfg in
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
        Face.False xi
      | _ ->
        let bnd = Option.get_exn obnd in
        let abs =
          lazy begin
            eval_abs
              {inner = {cfg.inner with tm = bnd};
               action = D.cmp (D.equate r r') cfg.action}
          end
        in
        Face.Indet (xi, abs)
    end
  | `Same _ ->
    let bnd = Option.get_exn obnd in
    let abs = lazy begin eval_abs @@ set_tm bnd cfg end in
    Face.True (r, r', abs)

and force_rigid_face face =
  match face with
  | Face.True (_, _, abs) ->
    raise @@ Proj (Lazy.force abs)
  | Face.False xi ->
    Face.False xi
  | Face.Indet (xi, abs) ->
    Face.Indet (xi, Lazy.force abs)

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

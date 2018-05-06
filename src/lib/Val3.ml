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
end

module Star :
sig
  type t
  type 'a m = [`Ok of 'a | `Same]

  val make : Dim.t -> Dim.t -> t m
  val unleash : t -> Dim.t * Dim.t
  val perm : P.t -> t -> t
  val restrict : R.t -> t -> t m
end =
struct
  type t = Dim.t * Dim.t
  type 'a m = [`Ok of 'a | `Same]

  let make c d =
    match Dim.compare c d with
    | D.Same ->
      `Same
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

type _ con =
  | Loop : Gen.t -> can con
  | Base : can con
  | Coe : {dir : Star.t; abs : abs; el : can t} -> can con
  | Pi : {dom : can t; cod : clo} -> can con
  | Bool : can con

and 'a cfg = {tm : 'a; rho : env; phi : R.t; pi : P.t}
and clo = Tm.chk Tm.bnd cfg
and env = can t list

and abs = {atom : atom; node : can t}
and 'a node = {con : 'a con; queue : frame list}
and 'a t = 'a node ref


module Val =
struct
  let enqueue f fs =
    match f, fs with
    | Restrict phi, Restrict phi' :: fs ->
      Restrict (R.union phi phi') :: fs
    | Perm pi, Perm pi' :: fs ->
      Perm (P.cmp pi pi') :: fs
    | _ ->
      f::fs

  let perm : type a. P.t -> a t -> a t =
    fun pi node ->
      ref @@ {!node with queue = enqueue (Perm pi) !node.queue}

  let restrict : type a. R.t -> a t -> a t =
    fun phi node ->
      ref @@ {!node with queue = enqueue (Restrict phi) !node.queue}
end

module Abs =
struct
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


module Clo =
struct
  let perm pi clo =
    {clo with pi = P.cmp pi clo.pi}
end


type 'a step = [`Ret of 'a con | `Step of 'a t]

let ret v = `Ret v
let step v = `Step v

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
      | Pi info ->
        let dom = Val.perm pi info.dom in
        let cod = Clo.perm pi info.cod in
        Pi {dom; cod}
      | Bool ->
        con

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

      | Coe info ->
        make_coe
          (Star.restrict phi info.dir)
          (lazy begin Abs.restrict phi info.abs end)
          (lazy begin Val.restrict phi info.el end)

      | _ -> failwith ""

  and make_coe mdir abs el : can step =
    match mdir with
    | `Ok dir ->
      rigid_coe dir (Lazy.force abs) (Lazy.force el)
    | `Same ->
      step @@ Lazy.force el

  and rigid_coe dir abs el : can step =
    let _, ty = Abs.unleash abs in
    match unleash ty with
    | Pi _ ->
      ret @@ Coe {dir; abs; el}
    | Bool ->
      step el
    | _ -> failwith ""

  and unleash : type a. a t -> a con =
    fun node ->
      let con = eval_queue !node.queue !node.con in
      node := {con; queue = []};
      con

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

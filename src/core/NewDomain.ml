open RedBasis.Bwd
open BwdNotation

type dim =
  | Atom of Name.t
  | Dim0
  | Dim1

type 'a face = (dim * dim) * 'a
type 'a sys = 'a face list
type 'a abs = Abs of Name.t bwd * 'a

(** This is the type of "prevalues", that is the domain from which values come.
    A prevalue can be judged to be a value with respect to a restriction / dimension
    theory. I think we will not write code that checks that something is a value, but instead
    make this involved in the pre-and-post- conditions of the semantic operations. *)
type value =
  | Pi of {dom : value; cod : clo}
  | Neu of {ty : value; neu : neu; sys : value sys}
  | Lam of clo
  | Cons of value * value
  | Up of {neu : neu; sys : value sys}

and head =
  | Lvl of int

and frame =
  | FunApp of value
  | Car

and neu =
  {head : head;
   frames : frame bwd}

and cell =
  | Val of value
  | Dim of dim

and env = cell bwd

and clo =
  | Clo of {tm : Tm.tm; env : env}



(** This should be the dimension equality oracle *)
module Rel :
sig
  type t
  val union : dim -> dim -> t -> t
end =
struct
  type t
  let union _ _ _ = failwith ""
end

(** Permutations *)
module Perm :
sig
  type t
  val freshen : Name.t bwd -> Name.t bwd * t
end =
struct
  type t
  let freshen _ = failwith ""
end

type rel = Rel.t
type perm = Perm.t

module type Domain =
sig
  type t

  (** [swap] is a purely syntactic operation which perserves the property of being a Ξ-value. *)
  val swap : perm -> t -> t

  (** [subst] is a purely syntactic operation that does {e not} preserve the property of being a Ξ-value; it should usually be followed by [run]. *)
  val subst : dim -> Name.t -> t -> t

  (** [run] brings the element underneath the restriction Ξ. *)
  val run : rel -> t -> t
end

module type DomainPlug =
sig
  include Domain
  val plug : rel -> frame -> t -> t
end

module rec Syn :
sig
  type t = Tm.tm
  val eval : rel -> env -> t -> value
end =
struct
  type t = Tm.tm
  let eval _ _ = failwith ""
end

and Clo :
sig
  type t = clo
  val inst : rel -> t -> cell -> value
end =
struct
  type t = clo

  let inst (rel : rel) clo cell : value =
    let Clo {tm; env} = clo in
    Syn.eval rel (env #< cell) tm
end

and Val : DomainPlug with type t = value =
struct
  type t = value

  module ValSys = Sys (Val)

  let run _ = failwith ""
  let swap _ = failwith ""
  let subst _ = failwith ""

  let plug rel frm hd =
    match frm, hd with
    | FunApp arg, Lam clo ->
      Clo.inst rel clo @@ Val arg

    | Car, Cons (v0, _) ->
      v0

    | _, Up info ->
      let neu = Neu.plug rel frm info.neu in
      let sys = ValSys.plug rel frm info.sys in
      Up {neu; sys}

    | _ ->
      failwith ""
end

and Neu : DomainPlug with type t = neu =
struct
  type t = neu

  let swap _ = failwith ""
  let run _ = failwith ""
  let plug _ = failwith ""
  let subst _ = failwith ""

  let plug rel frm neu =
    {neu with
     frames = neu.frames #< frm}
end

and Frame :
sig
  include Domain with type t = frame
  val occurs : Name.t bwd -> frame -> [`No | `Might]
end =
struct
  type t = frame
  let swap _ = failwith ""
  let subst _ = failwith ""
  let run _ = failwith ""

  let occurs xs =
    function
    | FunApp _ ->
      `Might
    | Car ->
      `No
end


and Sys : functor (X : DomainPlug) -> DomainPlug with type t = X.t sys =
  functor (X : DomainPlug) ->
  struct
    type t = X.t sys
    module Face = Face (X)

    let swap _ _ = failwith ""
    let subst _ _ = failwith ""
    let run _ _ = failwith ""

    let plug rel frm sys =
      List.map (Face.plug rel frm) sys
  end

and Face : functor (X : DomainPlug) -> DomainPlug with type t = X.t face =
  functor (X : DomainPlug) ->
  struct
    type t = X.t face

    let swap _ _ = failwith ""
    let subst _ _ = failwith ""
    let run _ _ = failwith ""

    let plug rel frm ((r, r'), bdy) =
      let rel' = Rel.union r r' rel in
      let frm' = Frame.run rel' frm in
      (r, r'), X.plug rel frm' bdy
  end

and Abs : functor (X : DomainPlug) -> DomainPlug with type t = X.t abs =
  functor (X : DomainPlug) ->
  struct
    type t = X.t abs

    let swap _ _ = failwith ""
    let subst _ _ = failwith ""
    let run _ _ = failwith ""

    let plug rel frm abs =
      let Abs (xs, a) = abs in
      match Frame.occurs xs frm with
      | `No ->
        let a' = X.plug rel frm a in
        Abs (xs, a')
      | `Might ->
        let ys, pi = Perm.freshen xs in
        let a' = X.plug rel frm @@ X.swap pi a in
        Abs (ys, a')

  end

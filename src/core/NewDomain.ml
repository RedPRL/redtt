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
  val hide : Name.t bwd -> t -> t

  val status : dim -> dim -> t -> [`Equal | `Apart | `Indet]
end =
struct
  type t
  let union _ _ _ = failwith ""
  let hide _ _ = failwith ""
  let status _ _ _ = failwith ""
end

(** Permutations *)
module Perm :
sig
  type t
  val freshen : Name.t bwd -> Name.t bwd * t
  val swap_name : t -> Name.t -> Name.t
end =
struct
  type t
  let freshen _ = failwith ""

  let swap_name _ = failwith ""
end

type rel = Rel.t
type perm = Perm.t

module type Domain =
sig
  type t

  (** [swap] is a purely syntactic operation which perserves the property of being a Ξ-value. *)
  val swap : perm -> t -> t

  (** [subst] is a purely syntactic operation that does {e not} preserve the property of being a Ξ-value; it should usually be followed by [run] with extended Ξ. *)
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

and Dim : Domain with type t = dim =
struct
  type t = dim
  let swap _ _ = failwith ""
  let subst _ _ = failwith ""
  let run _ r = r
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


and Sys :
  functor (X : DomainPlug) ->
  sig
    include DomainPlug with type t = X.t sys
    exception Triv of X.t
  end =
  functor (X : DomainPlug) ->
  struct
    type t = X.t sys
    module Face = Face (X)

    exception Triv of X.t

    let swap pi = List.map @@ Face.swap pi
    let subst r x = List.map @@ Face.subst r x

    let run rel sys =
      let run_face face =
        try [Face.run rel face]
        with
        | Face.Dead -> []
        | Face.Triv bdy -> raise @@ Triv bdy
      in
      List.flatten @@ List.map run_face sys

    let plug rel frm sys =
      List.map (Face.plug rel frm) sys
  end

and Face :
  functor (X : DomainPlug) ->
  sig
    include DomainPlug with type t = X.t face

    exception Triv of X.t
    exception Dead
  end =
  functor (X : DomainPlug) ->
  struct
    type t = X.t face

    exception Triv of X.t
    exception Dead

    let swap pi ((r, r'), bdy) =
      (Dim.swap pi r, Dim.swap pi r'), X.swap pi bdy

    let subst r x ((s, s'), bdy) =
      (Dim.subst r x s, Dim.subst r x s'), X.subst r x bdy

    let run rel ((r, r'), bdy) =
      match Rel.status r r' rel with
      | `Apart ->
        raise Dead
      | `Equal ->
        let bdy' = X.run rel bdy in
        raise @@ Triv bdy'
      | `Indet ->
        let rel' = Rel.union r r' rel in
        let bdy' = X.run rel' bdy in
        (r, r'), bdy'

    let plug rel frm ((r, r'), bdy) =
      let rel' = Rel.union r r' rel in
      let frm' = Frame.run rel' frm in
      (r, r'), X.plug rel frm' bdy
  end

and Abs : functor (X : DomainPlug) -> DomainPlug with type t = X.t abs =
  functor (X : DomainPlug) ->
  struct
    type t = X.t abs

    let swap pi abs =
      let Abs (xs, a) = abs in
      let xs' = Bwd.map (Perm.swap_name pi) xs in
      let a' = X.swap pi a in
      Abs (xs', a')

    let subst r z abs =
      let Abs (xs, a) = abs in
      let ys, pi = Perm.freshen xs in
      let a' = X.swap pi a in
      Abs (ys, a')

    let run rel abs =
      let Abs (xs, a) = abs in
      (* TODO: I think the following makes sense, but let's double check. The alternative is to freshen, but it seems like we don't need to if we can un-associate these names. *)
      let rel' = Rel.hide xs rel in
      let a' = X.run rel' a in
      Abs (xs, a')

    let plug rel frm abs =
      let Abs (xs, a) = abs in
      match Frame.occurs xs frm with
      | `No ->
        let a' = X.plug rel frm a in
        Abs (xs, a')
      | `Might ->
        let ys, pi = Perm.freshen xs in
        let rel' = Rel.hide xs rel in
        let a' = X.plug rel' frm @@ X.swap pi a in
        Abs (ys, a')

  end

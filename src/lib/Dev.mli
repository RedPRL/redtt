open RedBasis.Bwd

type tm = Tm.tm
type ty = Tm.tm

type 'a decl =
  | Hole
  | Defn of 'a

type status =
  | Blocked
  | Active

type ('a, 'b) equation =
  {ty0 : ty;
   tm0 : 'a;
   ty1 : ty;
   tm1 : 'b}

type param =
  | P of ty
  | Tw of ty * ty

type params = (Name.t * param) bwd

type 'a bind

type problem =
  | Unify of (tm, tm) equation
  | All of param * problem bind

type entry =
  | E of Name.t * ty * tm decl
  | Q of status * problem
  | Bracket of Name.t

val bind : Name.t -> problem -> problem bind
val unbind : problem bind -> Name.t * problem


val pp_entry : entry Pretty.t0


type twin = Tm.twin

module Subst = GlobalCx

module type DevSort =
sig
  include Occurs.S
  val subst : Subst.t -> t -> t
end

module Problem :
sig
  include DevSort with type t = problem
  val eqn : ty0:ty -> tm0:tm -> ty1:ty -> tm1:tm -> problem
  val all : Name.t -> ty -> problem -> problem
  val all_twins : Name.t -> ty -> ty -> problem -> problem
end

module Param : DevSort with type t = param

module Params : Occurs.S with type t = param bwd

module Equation :
sig
  include DevSort with type t = (tm, tm) equation
  val sym : ('a, 'b) equation -> ('b, 'a) equation
end

module Decl : Occurs.S with type t = tm decl
module Entry : DevSort with type t = entry
module Entries : Occurs.S with type t = entry list

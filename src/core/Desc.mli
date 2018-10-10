open Tm

(** Recursive argument types; currently this includes only [Self]; in the future, this will be extended with an indexed
    version of [Self], as well a formal function type. *)
type rec_spec =
  | Self

type arg_spec =
  [ `Const of tm
  | `Rec of rec_spec
  | `Dim
  ]


type ('a, 'e) telescope =
  | TNil of 'e
  | TCons of 'a * ('a, 'e) telescope Tm.bnd

type constr = (arg_spec, (tm, tm) system) telescope

module Constr :
sig
  include LocallyNameless.S with type t = constr
  val bind : Name.t -> t -> t TmData.bnd

  val specs : t -> (string option * arg_spec) list
  val boundary : t -> (tm, tm) system

  val pp : t Pp.t0
end

type param = tm
type constrs = (string * constr) list
type body = (param, constrs) telescope

module Body :
sig
  include LocallyNameless.S with type t = body
  val bind : Name.t -> t -> t Tm.bnd

  (** Invariant: first argument is locally closed. *)
  val unbind_with : Tm.tm Tm.cmd -> t Tm.bnd -> t

  (** Invariant: first argument is locally closed. *)
  val instance : Tm.tm list -> t -> constrs
end

type desc =
  {kind : Kind.t;
   lvl : Lvl.t;
   body : body;
   status : [`Complete | `Partial]}

val constrs : desc -> constrs
val add_constr : desc -> string * constr -> desc


exception ConstructorNotFound of string
val lookup_constr : string -> constrs -> constr

(** Returns 'yes' if the description specifies strictly no higher dimensional structure, like the natural numbers. *)
val is_strict_set : desc -> bool

val pp_constr : ?dlbl:string -> constr Pp.t
val pp_constrs : ?dlbl:string -> constrs Pp.t
val pp_desc : ?dlbl:string -> desc Pp.t

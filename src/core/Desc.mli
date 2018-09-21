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
  val specs : t -> (string option * arg_spec) list
  val boundary : t -> (tm, tm) system
end


type desc =
  {kind : Kind.t;
   lvl : Lvl.t;
   params : (string * tm) list;
   constrs : (string * constr) list;
   status : [`Complete | `Partial]}


exception ConstructorNotFound of string
val lookup_constr : string -> desc -> constr

(** Returns 'yes' if the description specifies strictly no higher dimensional structure, like the natural numbers. *)
val is_strict_set : desc -> bool

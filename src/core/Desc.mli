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


type constr =
  {specs : (string * arg_spec) list;
   boundary : (tm, tm) system}

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

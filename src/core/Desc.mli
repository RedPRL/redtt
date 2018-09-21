(** Recursive argument types; currently this includes only [Self]; in the future, this will be extended with an indexed
    version of [Self], as well a formal function type. *)
type 'a rec_spec =
  | Self

type 'a face = 'a * 'a * 'a option
type 'a system = 'a face list

type 'a arg_spec =
  [ `Const of 'a
  | `Rec of 'a rec_spec
  | `Dim
  ]


type 'a constr =
  {specs : (string * 'a arg_spec) list;
   boundary : 'a system}


(** A datatype description is just a list of named constructors. *)
type 'a desc =
  {kind : Kind.t;
   lvl : Lvl.t;
   params : (string * 'a) list;
   constrs : (string * 'a constr) list;
   status : [`Complete | `Partial]}

exception ConstructorNotFound of string
val lookup_constr : string -> 'a desc -> 'a constr

(** Returns 'yes' if the description specifies strictly no higher dimensional structure, like the natural numbers. *)
val is_strict_set : 'a desc -> bool

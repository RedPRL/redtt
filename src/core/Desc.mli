(** Recursive argument types; currently this includes only [Self]; in the future, this will be extended with an indexed
    version of [Self], as well a formal function type. *)
type 'a rec_spec =
  | Self

(* TODO: abstract *)
type data_label = string
type con_label = string

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

val dim_specs : 'a constr -> string list
val const_specs : 'a constr -> (string * 'a) list
val rec_specs : 'a constr -> (string * 'a rec_spec) list


(** A datatype description is just a list of named constructors. *)
type 'a desc =
  {kind : Kind.t;
   lvl : Lvl.t;
   constrs : (con_label * 'a constr) list;
   status : [`Complete | `Partial]}

exception ConstructorNotFound of con_label
val lookup_constr : con_label -> 'a desc -> 'a constr

(** Returns 'yes' if the description specifies strictly no higher dimensional structure, like the natural numbers. *)
val is_strict_set : 'a desc -> bool


val pp_data_label : data_label Pp.t0
val pp_con_label : con_label Pp.t0

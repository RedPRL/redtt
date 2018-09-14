(** Recursive argument types; currently this includes only [Self]; in the future, this will be extended with an indexed
    version of [Self], as well a formal function type. *)
type 'a rec_spec =
  | Self

(* TODO: abstract *)
type data_label = string
type con_label = string

type 'a face = 'a * 'a * 'a option
type 'a system = 'a face list

(** A data constructor is a list of parameters (non-recursive arguments) and recursive arguments,
    and dimensions.

    When we generalized to indexed inductive types, the parameters will become {e bound} in the
    arguments. TODO: rename [args] to [rec_args]. *)
type 'a constr =
  {const_specs : (string * 'a) list;
   rec_specs : (string * 'a rec_spec) list;
   dim_specs : string list;
   boundary : 'a system}


(** A datatype description is just a list of named constructors. *)
type 'a desc =
  {kind : Kind.t;
   lvl : Lvl.t;
   constrs : (con_label * 'a constr) list}

exception ConstructorNotFound of con_label
val lookup_constr : con_label -> 'a desc -> 'a constr

(** Returns 'yes' if the description specifies strictly no higher dimensional structure, like the natural numbers. *)
val is_strict_set : 'a desc -> bool


val pp_data_label : data_label Pp.t0
val pp_con_label : con_label Pp.t0

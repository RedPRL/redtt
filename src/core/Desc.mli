(** Recursive argument types; currently this includes only [Self]; in the future, this will be extended with an indexed
    version of [Self], as well a formal function types. *)
type 'a arg_ty =
  | Self

type 'a tele = 'a list

(** A data constructor is a list of parameters (non-recursive arguments) and recursive arguments.
    When we generalized to indexed inductive types, the parameters will become *bound* in the arguments. Finally, to support HITs,
    we will ultimately add dimension arguments and boundary constraints. *)
type 'a constr =
  {params : (string * 'a) tele;
   args : 'a arg_ty list;
   dims : string list}

(* TODO: abstract *)
type data_label = string
type con_label = string


(** A datatype description is just a list of named constructors. *)
type 'a desc = (con_label * 'a constr) list

exception ConstructorNotFound of con_label
val lookup_constr : con_label -> 'a desc -> 'a constr

(** Returns 'yes' if the description specifies strictly higher dimensional structure, like the strict natural numbers.
    Currently, this is always true but will change as we extend to support higher inductive types. *)
val is_strict_set : 'a desc -> bool


val pp_data_label : data_label Pretty.t0
val pp_con_label : con_label Pretty.t0

val pp_desc : 'a Pretty.t -> 'a desc Pretty.t0
val pp_constr : 'a Pretty.t -> 'a constr Pretty.t0

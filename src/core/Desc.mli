(** Recursive argument types; currently this includes only [Self]; in the future, this will be extended with an indexed
    version of [Self], as well a formal function type. *)
type 'a arg_ty =
  | Self

(* TODO: abstract *)
type data_label = string
type con_label = string

module Boundary :
sig
  type ('var, 'a) term =
    | Var of 'var
    | Intro of con_label * 'a list * ('var, 'a) term list
    (* TODO: fhcom, lam, app *)

  type ('var, 'a) face = 'a * 'a * ('var, 'a) term
  type ('var, 'a) sys = ('var, 'a) face list
end



(** A data constructor is a list of parameters (non-recursive arguments) and recursive arguments.
    When we generalized to indexed inductive types, the parameters will become *bound* in the arguments. Finally, to support HITs,
    we will ultimately add dimension arguments and boundary constraints. *)
type ('var, 'a) constr =
  {params : (string * 'a) list;
   args : (string * 'a arg_ty) list;
   dims : string list}


(** A datatype description is just a list of named constructors. *)
type ('var, 'a) desc = (con_label * ('var, 'a) constr) list

exception ConstructorNotFound of con_label
val lookup_constr : con_label -> ('var, 'a) desc -> ('var, 'a) constr

(** Returns 'yes' if the description specifies strictly no higher dimensional structure, like the natural numbers. *)
val is_strict_set : ('var, 'a) desc -> bool


val pp_data_label : data_label Pp.t0
val pp_con_label : con_label Pp.t0

val pp_desc : 'var Pp.t -> 'a Pp.t -> ('var, 'a) desc Pp.t0
val pp_constr : 'var Pp.t -> 'a Pp.t -> ('var, 'a) constr Pp.t0

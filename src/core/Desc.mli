(** Recursive argument types; currently this includes only [Self]; in the future, this will be extended with an indexed
    version of [Self], as well a formal function type. *)
type 'a arg_ty =
  | Self

(* TODO: abstract *)
type data_label = string
type con_label = string

module Boundary :
sig
  (** ['var] is the representation of variables; ['r] is the representation of dimensions;
      ['a] is the representation of ordinary terms. *)
  type ('var, 'r, 'a) term =
    | Var of 'var
    | Intro of
        { clbl : con_label;
          const_args : 'a list;
          rec_args : ('var, 'r, 'a) term list;
          rs : 'r list}
    (* TODO: fhcom, lam, app *)

  type ('var, 'r, 'a) face = 'r * 'r * ('var, 'r, 'a) term
  type ('var, 'r, 'a) sys = ('var, 'r, 'a) face list
end


(** A data constructor is a list of parameters (non-recursive arguments) and recursive arguments,
    and dimensions.

    When we generalized to indexed inductive types, the parameters will become {e bound} in the
    arguments. TODO: rename [params] to [const_args] and [args] to [rec_args]. *)
type ('var, 'r, 'a) constr =
  {params : (string * 'a) list;
   args : (string * 'a arg_ty) list;
   dims : string list}


(** A datatype description is just a list of named constructors. *)
type ('var, 'r, 'a) desc = (con_label * ('var, 'r, 'a) constr) list

exception ConstructorNotFound of con_label
val lookup_constr : con_label -> ('var, 'r, 'a) desc -> ('var, 'r, 'a) constr

(** Returns 'yes' if the description specifies strictly no higher dimensional structure, like the natural numbers. *)
val is_strict_set : ('var, 'r, 'a) desc -> bool


val pp_data_label : data_label Pp.t0
val pp_con_label : con_label Pp.t0

val pp_desc : 'var Pp.t -> 'a Pp.t -> ('var, 'r, 'a) desc Pp.t0
val pp_constr : 'var Pp.t -> 'a Pp.t -> ('var, 'r, 'a) constr Pp.t0

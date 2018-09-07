(** Recursive argument types; currently this includes only [Self]; in the future, this will be extended with an indexed
    version of [Self], as well a formal function type. *)
type 'a rec_spec =
  | Self

(* TODO: abstract *)
type data_label = string
type con_label = string

module Boundary :
sig
  (** ['var] is the representation of variables; ['r] is the representation of dimensions;
      ['a] is the representation of ordinary terms. *)
  type 'a term =
    | Var of int
    | Intro of
        { clbl : con_label;
          const_args : 'a list;
          rec_args : 'a term list;
          rs : 'a list}
    (* TODO: fhcom, lam, app *)

  type ('a, 'b) face = 'a * 'a * 'b
  type ('a, 'b) sys = ('a, 'b) face list
end


(** A data constructor is a list of parameters (non-recursive arguments) and recursive arguments,
    and dimensions.

    When we generalized to indexed inductive types, the parameters will become {e bound} in the
    arguments. TODO: rename [args] to [rec_args]. *)
type ('a, 'b) constr =
  {const_specs : (string * 'a) list;
   rec_specs : (string * 'a rec_spec) list;
   dim_specs : string list;
   boundary : ('a, 'b) Boundary.sys}


(** A datatype description is just a list of named constructors. *)
type ('a, 'b) desc =
  {params : (string * 'a) list;
   kind : Kind.t;
   lvl : Lvl.t;
   constrs : (con_label * ('a, 'b) constr) list}

exception ConstructorNotFound of con_label
val lookup_constr : con_label -> ('a, 'b) desc -> ('a, 'b) constr

(** Returns 'yes' if the description specifies strictly no higher dimensional structure, like the natural numbers. *)
val is_strict_set : ('a, 'b) desc -> bool


val pp_data_label : data_label Pp.t0
val pp_con_label : con_label Pp.t0

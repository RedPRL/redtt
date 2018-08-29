open RedBasis.Bwd
include module type of DomainData

val clo_name : clo -> string option

val pp_abs : Format.formatter -> abs -> unit
val pp_ext_abs : Format.formatter -> ext_abs -> unit
val pp_value : Format.formatter -> value -> unit
val pp_dims : Format.formatter -> I.t list -> unit
val pp_neu : Format.formatter -> neu -> unit
val pp_comp_face : Format.formatter -> rigid_abs_face -> unit
val pp_val_face : Format.formatter -> ('x, value) face -> unit
val pp_val_sys : Format.formatter -> ('x, value) face list -> unit
val pp_comp_sys : Format.formatter -> comp_sys -> unit
val pp_names : Format.formatter -> Name.t bwd -> unit

val pp_clo : Format.formatter -> clo -> unit
val pp_nclo : Format.formatter -> nclo -> unit

val pp_env_cell : Format.formatter -> env_el -> unit
val pp_env : Format.formatter -> env -> unit


exception ProjAbs of abs
exception ProjVal of value

val force_val_face : val_face -> ('a, value) face option
val force_abs_face : ([`Any], abs) face -> ('a, abs) face option
val force_val_sys : val_face list -> [`Ok of ('a, value) face list | `Proj of value]
val force_abs_sys : ([`Any], abs) face list -> [`Ok of ('a, abs) face list | `Proj of abs]


module Env :
sig
  include Sort.S
    with type t = env
    with type 'a m = 'a
  val emp : env
  val clear_locals : env -> env

  (* What direction do these go? Think of the environment as a snoc list, where things are projected by counting from the *right*.
     So, if I have an environment [E], then [append E [x0; x1; x2]] is [E #< x0 #< x1 #< x2]
  *)

  val snoc : env -> env_el -> env
  val append : env -> env_el list -> env
end

module Value : Sort.S
  with type t = value
  with type 'a m = 'a

module Neu : Sort.S
  with type t = neu
  with type 'a m = 'a

module Nf : Sort.S
  with type t = nf
  with type 'a m = 'a


module NeuAbs : IAbs.S
  with type el = neu * val_sys

module ExtAbs : IAbs.S
  with type el = value * val_sys

module Abs : IAbs.S
  with type el = value

module ValFace : Face.S with type body := value
module AbsFace : Face.S with type body := abs

module Clo : Sort.S
  with type t = clo
  with type 'a m = 'a

module NClo : Sort.S
  with type t = nclo
  with type 'a m = 'a


module TickClo : Sort.S
  with type t = tick_clo
  with type 'a m = 'a

module CompSys :
sig
  include Sort.S
    with type t = comp_sys
    with type 'a m = [`Ok of comp_sys | `Proj of abs]
  val forall : I.atom -> t -> t
  val forallm : I.atom -> t m -> t m
end

module BoxSys : Sort.S
  with type t = box_sys
  with type 'a m = [`Ok of box_sys | `Proj of value]

module ValSys :
sig
  include Sort.S
    with type t = val_sys
    with type 'a m = 'a

  val from_rigid : rigid_val_sys -> t
  val forall : I.atom -> t -> t
end


val make : con -> value
val make_later : value -> value

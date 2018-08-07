open RedBasis.Bwd
include module type of DomainData

val clo_name : clo -> string option
val nclo_names : nclo -> string option bwd

val pp_abs : Format.formatter -> abs -> unit
val pp_value : Format.formatter -> value -> unit
val pp_dims : Format.formatter -> I.t list -> unit
val pp_neu : Format.formatter -> neu -> unit
val pp_comp_face : Format.formatter -> rigid_abs_face -> unit
val pp_val_face : Format.formatter -> ('x, value) face -> unit
val pp_val_sys : Format.formatter -> ('x, value) face list -> unit
val pp_comp_sys : Format.formatter -> comp_sys -> unit
val pp_names : Format.formatter -> Name.t bwd -> unit


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
  val push : env_el -> env -> env
  val push_many : env_el list -> env -> env
end

module Value : Sort.S
  with type t = value
  with type 'a m = 'a


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

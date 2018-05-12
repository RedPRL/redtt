type value = Val.value

module Cx :
sig
  type t

  val emp : t

  val ext_ty : t -> nm:string option -> value -> t * value
  val ext_el : t -> nm:string option -> ty:value -> el:value -> t

  val eval : t -> 'a Tm.t -> value

  val ppenv : t -> Pretty.env

  val lookup : int -> t -> [`Ty of value | `Dim]
  val check_eq : t -> ty:value -> value -> value -> unit
  val check_subtype : t -> value -> value -> unit
end

type cx = Cx.t

val check : cx -> Val.value -> Tm.chk Tm.t -> unit
val infer : cx -> Tm.inf Tm.t -> value

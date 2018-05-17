type value = Val.value

module Cx :
sig
  type t

  val emp : t

  val ext_ty : t -> nm:string option -> value -> t * value
  val ext_dim : t -> nm:string option -> t * Val.atom
  val ext_dims : t -> nms:string option list -> t * Val.atom list

  val def : t -> nm:string option -> ty:value -> el:value -> t

  val eval : t -> 'a Tm.t -> value
  val eval_tm_sys : t -> Tm.chk Tm.t Tm.system -> Val.val_sys

  val ppenv : t -> Pretty.env

  val lookup : int -> t -> [`Ty of value | `Dim]
  val check_eq : t -> ty:value -> value -> value -> unit
  val check_subtype : t -> value -> value -> unit

  val quote : t -> ty:value -> value -> Tm.chk Tm.t
  val quote_ty : t -> value -> Tm.chk Tm.t
end

type cx = Cx.t

val check : cx -> Val.value -> Tm.chk Tm.t -> unit
val infer : cx -> Tm.inf Tm.t -> value

val check_boundary : cx -> Val.value -> Val.val_sys -> Tm.chk Tm.t -> unit

type cx
type t = cx

module type S =
sig
  type t = cx

  module Eval : Val2.S

  type value = Val2.value

  val emp : t

  val ext_ty : t -> nm:string option -> value -> t * value
  val ext_dim : t -> nm:string option -> t * I.atom
  val ext_dims : t -> nms:string option list -> t * I.atom list

  val restrict : t -> I.t -> I.t -> t

  val def : t -> nm:string option -> ty:value -> el:value -> t

  val ppenv : t -> Pretty.env
  val lookup : int -> t -> [`Ty of value | `Dim]

  val eval : t -> Tm.tm -> value
  val eval_cmd : t -> Tm.tm Tm.cmd -> value
  val eval_head : t -> Tm.tm Tm.head -> value
  val eval_frame : t -> value -> Tm.tm Tm.frame -> value
  val eval_dim : t -> Tm.tm -> I.t
  val eval_tm_sys : t -> (Tm.tm, Tm.tm) Tm.system -> Val2.val_sys

  val check_eq : t -> ty:value -> value -> value -> unit
  val check_subtype : t -> value -> value -> unit

  val quote : t -> ty:value -> value -> Tm.tm
  val quote_ty : t -> value -> Tm.tm

  val check_eq_ty : t -> value -> value -> unit
end

module M (V : Val2.S) : S with type t = t

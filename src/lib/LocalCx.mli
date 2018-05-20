type t

module type S =
sig
  type t

  type value = Val.value

  val emp : t

  val ext_ty : t -> nm:string option -> value -> t * value
  val ext_dim : t -> nm:string option -> t * Val.atom
  val ext_dims : t -> nms:string option list -> t * Val.atom list

  val restrict : t -> Dim.repr -> Dim.repr -> t

  val def : t -> nm:string option -> ty:value -> el:value -> t

  val ppenv : t -> Pretty.env
  val lookup : int -> t -> [`Ty of value | `Dim]

  val eval : t -> 'a Tm.t -> value
  val eval_dim : t -> Tm.chk Tm.t -> Dim.repr
  val eval_tm_sys : t -> Tm.chk Tm.t Tm.system -> Val.val_sys

  val check_eq : t -> ty:value -> value -> value -> unit
  val check_subtype : t -> value -> value -> unit

  val quote : t -> ty:value -> value -> Tm.chk Tm.t
  val quote_ty : t -> value -> Tm.chk Tm.t

  val check_eq_ty : t -> value -> value -> unit

  val unleash_dim : t -> Dim.repr -> Dim.t
  val compare_dim : t -> Dim.repr -> Dim.repr -> Dim.compare
  val equate_dim : t -> Dim.repr -> Dim.repr -> Dim.action
end

module M (V : Val.S) : S with type t := t

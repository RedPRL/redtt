(* local context *)

type t

val emp : t
val ext : t -> Val.can Val.t -> t
val def : t -> ty:Val.can Val.t -> tm:Val.can Val.t -> t
val proj : t -> t

include DimRel.S with type t := t

val lookup : int -> t -> Val.can Val.t
val len : t -> int

val env : t -> Val.env
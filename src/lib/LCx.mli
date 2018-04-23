(* local context *)

type t

val emp : t
val ext : t -> Val.can Val.t -> t
val def : t -> ty:Val.can Val.t -> tm:Val.can Val.t -> t

val proj: t -> t option
val proj_exn : t -> t

type view = 
  | Snoc of {cx : t; ty : Val.can Val.t; def : Val.can Val.t}
  | Nil

val view : t -> view

include DimRel.S with type t := t

val lookup : int -> t -> Val.can Val.t
val len : t -> int

val env : t -> Val.env
val ppenv : t -> Tm.Pretty.Env.t
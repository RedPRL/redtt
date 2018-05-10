module Env :
sig
  type t

  val len : t -> int

  val make : int -> t
  val succ : t -> t
  val abs : t -> Symbol.t -> t

  val ix_of_lvl : int -> t -> int
  val ix_of_atom : Symbol.t -> t -> int
end

val quote_nf : Env.t -> Val.nf -> Tm.chk Tm.t
val quote_neu : Env.t -> Val.neu -> Tm.inf Tm.t

val equiv : Env.t -> ty:Val.value -> Val.value -> Val.value -> bool

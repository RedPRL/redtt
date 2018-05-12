module Env :
sig
  type t

  val len : t -> int

  val emp : t
  val make : int -> t
  val succ : t -> t
  val abs : t -> Symbol.t -> t

  val ix_of_lvl : int -> t -> int
  val ix_of_atom : Symbol.t -> t -> int
end

type env = Env.t

val quote_nf : env -> Val.nf -> Tm.chk Tm.t
val quote_neu : env -> Val.neu -> Tm.inf Tm.t

val equiv : env -> ty:Val.value -> Val.value -> Val.value -> unit
val subtype : env -> Val.value -> Val.value -> unit

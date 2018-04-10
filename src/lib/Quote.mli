type neu_quo = {tm : Tm.inf Tm.t; ty : Val.can Val.t}

module Ctx :
sig
  type t
  val len : t -> int
  val nth : t -> int -> Val.can Val.t
  
  val emp : t
  val ext : t -> Val.can Val.t -> t
end

type ctx = Ctx.t

val quote_can : ctx:ctx -> ty:Val.can Val.t -> can:Val.can Val.t -> Tm.chk Tm.t
val quote_neu : ctx:ctx -> neu:Val.neu Val.t -> neu_quo

val equiv : ctx:ctx -> ty:Val.can Val.t -> can0:Val.can Val.t -> can1:Val.can Val.t -> unit
val approx : ctx:ctx -> ty:Val.can Val.t -> can0:Val.can Val.t -> can1:Val.can Val.t -> unit
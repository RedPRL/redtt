module Mode : 
sig
  type t

  val facon_de_parler : t
  val ontologically_real : t
end

module Ctx :
sig
  type t
  val emp : t
  val ext : t -> Val.can Val.t -> t
end

type ctx = Ctx.t
type mode = Mode.t

val check : mode:mode -> ctx:ctx -> ty:Val.can Val.t -> tm:Tm.chk Tm.t -> unit
val infer : mode:mode -> ctx:ctx -> tm:Tm.inf Tm.t -> Val.can Val.t
type cx = LCx.t
type mcx = MCx.t

val check : mcx:mcx -> cx:cx -> ty:Val.can Val.t -> tm:Tm.chk Tm.t -> unit
val infer : mcx:mcx -> cx:cx -> tm:Tm.inf Tm.t -> Val.can Val.t

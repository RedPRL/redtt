type cx = LCx.t

val check : cx:cx -> ty:Val.can Val.t -> tm:Tm.chk Tm.t -> unit
val infer : cx:cx -> tm:Tm.inf Tm.t -> Val.can Val.t
type ctx = LCx.t

val check : ctx:ctx -> ty:Val.can Val.t -> tm:Tm.chk Tm.t -> unit
val infer : ctx:ctx -> tm:Tm.inf Tm.t -> Val.can Val.t
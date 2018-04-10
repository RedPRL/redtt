type ctx

val check : ctx:ctx -> ty:Val.can Val.t -> tm:Tm.chk -> unit
val infer : ctx:ctx -> tm:Tm.inf -> Val.can Val.t
val check : ctx:Ctx.t -> ty:Val.can Val.t -> tm:Tm.chk -> unit
val infer : ctx:Ctx.t -> tm:Tm.inf -> Val.can Val.t
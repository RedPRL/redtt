type ctx

type mode = Rel | Irrel

val check : mode:mode -> ctx:ctx -> ty:Val.can Val.t -> tm:Tm.chk Tm.t -> unit
val infer : mode:mode -> ctx:ctx -> tm:Tm.inf Tm.t -> Val.can Val.t
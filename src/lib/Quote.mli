type neu_quo = {tm : Tm.inf Tm.t; ty : Val.can Val.t}

type ctx

val quote_can : ctx:ctx -> ty:Val.can Val.t -> can:Val.can Val.t -> Tm.chk Tm.t
val quote_neu : ctx:ctx -> neu:Val.neu Val.t -> neu_quo
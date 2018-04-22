val quote_can : n:int -> ty:Val.can Val.t -> can:Val.can Val.t -> Tm.chk Tm.t
val quote_neu : n:int -> neu:Val.neu Val.t -> Tm.inf Tm.t

val equiv : n:int -> ty:Val.can Val.t -> can0:Val.can Val.t -> can1:Val.can Val.t -> unit
val approx : n:int -> ty:Val.can Val.t -> can0:Val.can Val.t -> can1:Val.can Val.t -> unit
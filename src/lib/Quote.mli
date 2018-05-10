val quote_nf : int -> Val.nf -> Tm.chk Tm.t
val quote_neu : int -> Val.neu -> Tm.inf Tm.t

val equiv : int -> ty:Val.value -> Val.value -> Val.value -> bool

val quote : int -> ty:Val.can Val.t -> Val.can Val.t -> Tm.chk Tm.t
val equiv : int -> ty:Val.can Val.t -> Val.can Val.t -> Val.can Val.t -> Tm.chk Tm.t

val equiv_ty : int -> Val.can Val.t -> Val.can Val.t -> Tm.chk Tm.t
val quote_ty : int -> Val.can Val.t -> Tm.chk Tm.t
val approx_ty : int -> Val.can Val.t -> Val.can Val.t -> unit
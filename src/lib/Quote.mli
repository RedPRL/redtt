type el = Val.can Val.t
type tm = Tm.chk Tm.t

val quote : int -> ty:el -> el -> tm
val equiv : int -> ty:el -> el -> el -> tm

val equiv_ty : int -> el -> el -> tm
val quote_ty : int -> el -> tm
val approx_ty : int -> el -> el -> unit
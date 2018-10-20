module D = NewDomain
module Q = NewQuote
module Cx = NewCx

val check_ty : Cx.t -> Kind.t -> Tm.tm -> Lvl.t
val check_of_ty : Cx.t -> D.con -> D.con D.sys -> Tm.tm -> unit

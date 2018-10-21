module D = NewDomain
module Q = NewQuote
module Cx = NewCx

val check_ty : Cx.t -> Kind.t -> Tm.tm -> Lvl.t
val check_of_ty : Cx.t -> D.con -> D.con D.sys -> Tm.tm -> unit
val infer_ty : Cx.t -> Tm.tm Tm.cmd -> D.con

val quote : Cx.t -> D.con -> D.con -> Tm.tm
val quote_ty : Cx.t -> D.con -> Tm.tm

val check_subtype : Cx.t -> D.con -> D.con -> unit

val eval : Cx.t -> Tm.tm -> D.con
val eval_dim : Cx.t -> Tm.tm -> D.dim

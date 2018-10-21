module D = NewDomain
module Q = NewQuote

type t

val init : GlobalEnv.t -> t

val rel : t -> NewRestriction.t
val genv : t -> GlobalEnv.t
val venv : t -> D.Env.t
val qenv : t -> Q.QEnv.t

val extend : t -> ?name:string option -> D.con -> t * D.con
val extend_dim : t -> name:string option -> t * Name.t
val extend_dims : t -> names:string option list -> t * Name.t list
val lookup : t -> int -> [`Dim | `El of D.con]
val lookup_const : t -> ?tw:Tm.twin -> ?ushift:int -> Name.t -> [`Dim | `El of D.con]

val restrict : t -> D.dim -> D.dim -> t D.Rel.m
val restrict_ : t -> D.dim -> D.dim -> t

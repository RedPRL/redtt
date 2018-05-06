type t
type atom = Symbol.t
type dim = DimVal.t

val emp : t
val swap : atom -> atom -> t
val cmp : t -> t -> t
val lookup : atom -> t -> atom
val read : dim -> t -> dim

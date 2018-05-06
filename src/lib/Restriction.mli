type atom = Symbol.t
type dim = DimVal.t

type t

val emp : t
val equate : dim -> dim -> t
val union : t -> t -> t
val perm : Permutation.t -> t -> t

val compare : dim -> dim -> t -> DimVal.compare

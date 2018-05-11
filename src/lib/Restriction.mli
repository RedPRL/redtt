type atom = Symbol.t
type dim = Dim.t

type t

val emp : t
val equate : dim -> dim -> t
val union : t -> t -> t

val compare : dim -> dim -> t -> Dim.compare

val unleash : dim -> t -> dim

exception Inconsistent

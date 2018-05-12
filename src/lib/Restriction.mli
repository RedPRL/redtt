type atom = Symbol.t
type dim = Dim.repr

type t

val emp : t
val equate : dim -> dim -> t -> t

val compare : dim -> dim -> t -> Dim.compare

val canonize : dim -> t -> dim
val unleash : dim -> t -> Dim.t

exception Inconsistent



val pp : Format.formatter -> t -> unit

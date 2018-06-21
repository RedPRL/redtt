type atom = I.atom
type dim = I.t

type t

val emp : unit -> t
val equate : dim -> dim -> t -> t

val compare : dim -> dim -> t -> I.compare

exception Inconsistent


val as_action : t -> I.action
val pp : Format.formatter -> t -> unit

type atom = I.atom
type dim = I.t

type t

val emp : unit -> t
val equate : dim -> dim -> t -> t (* May raise I.Inconsistent *)
val hide : atom -> t -> t
val subst : dim -> atom -> t -> t
val swap : atom -> atom -> t -> t
val compare : dim -> dim -> t -> I.compare

val pp : Format.formatter -> t -> unit

type atom = I.atom
type dim = I.t

type t

val emp : unit -> t

val hide : atom -> t -> t

(* May raise I.Inconsistent *)
val equate : dim -> dim -> t -> t

val compare : dim -> dim -> t -> I.compare

val pp : Format.formatter -> t -> unit

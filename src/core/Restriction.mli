type atom = I.atom
type dim = I.t

type t

val emp : unit -> t

(* May raise I.Inconsistent *)
val equate : dim -> dim -> t -> t

val compare : dim -> dim -> t -> bool

val as_action : t -> I.action
val pp : Format.formatter -> t -> unit

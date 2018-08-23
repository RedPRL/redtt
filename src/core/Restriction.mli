type atom = I.atom
type dim = I.t

type t

val emp : unit -> t

(* May raise I.Inconsistent *)
val equate : dim -> dim -> t -> t * I.action

val compare : dim -> dim -> t -> I.compare

val act : I.action -> t -> t

val as_action : t -> I.action
val pp : Format.formatter -> t -> unit

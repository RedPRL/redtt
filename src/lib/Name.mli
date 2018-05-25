(** TODO: just merge this module with Symbol *)

type t

val const : string -> t
val fresh : unit -> t

val from_symbol : Symbol.t -> t
val symbol : t -> Symbol.t

val pp : t Pretty.t0

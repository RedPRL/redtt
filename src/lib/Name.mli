include Map.OrderedType

val const : string -> t

val named : string option -> t
val fresh : unit -> t

val to_string : t -> string

val pp : t Pretty.t0

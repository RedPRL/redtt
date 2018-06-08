include Map.OrderedType

val const : string -> t

val named : string option -> t
val fresh : unit -> t

val to_string : t -> string
val name : t -> string option

val pp : t Pretty.t0

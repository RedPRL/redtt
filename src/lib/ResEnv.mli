type t
val init : t
val bind : string -> t -> t
val bindn : string list -> t -> t
val bind_opt : string option -> t -> t

val get : string -> t -> int

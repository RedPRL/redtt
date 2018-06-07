type t
val init : t
val bind : string -> t -> t
val bindn : string list -> t -> t
val bind_opt : string option -> t -> t
val global : string -> Name.t -> t -> t

val get : string -> t -> [`Ix of int | `Ref of Name.t]

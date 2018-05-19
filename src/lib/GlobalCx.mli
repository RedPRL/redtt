type t
type value = Val.value

val emp : t
val define : t -> string -> ty:value -> el:value -> t
val add_hole : t -> string -> ty:value -> t

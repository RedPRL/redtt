type t = [`Omega | `Const of int]

val greater : t -> t -> bool
val lte : t -> t -> bool
val shift : int -> t -> t
val pp : t Pp.t0

val max : t -> t -> t

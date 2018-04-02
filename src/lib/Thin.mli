type 'x t
type t0 = Void.t t

val id : 'x t
val keep : 'x t -> 'x t
val skip : 'x t -> 'x t
val sub : 'x t -> 'x -> 'x t
val cmp : t0 -> t0 -> t0

val act : t0 -> 'a list -> 'a list
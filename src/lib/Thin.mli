type t

val id : t
val keep : t -> t
val skip : t -> t
val cmp : t -> t -> t

val proj : t -> 'a list -> 'a

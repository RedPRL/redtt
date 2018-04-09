type t

val id : t
val keep : t -> t
val skip : t -> t
val cmp : t -> t -> t

val act : t -> 'a list -> 'a list
val proj : t -> 'a list -> 'a

val from_ix : int -> t
type 'a t = 'a option
val map : ('a -> 'b) -> 'a t -> 'b t

val get_exn : 'a t -> 'a
exception WasNone
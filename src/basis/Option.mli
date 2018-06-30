type 'a t = 'a option
val map : ('a -> 'b) -> 'a t -> 'b t
val filter_map : ('a -> 'b option) -> 'a list -> 'b list
val get_exn : 'a t -> 'a
exception WasNone

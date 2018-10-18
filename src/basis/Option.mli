type 'a t = 'a option
val map : ('a -> 'b) -> 'a t -> 'b t
val foreach : 'a t -> ('a -> 'b) -> 'b t
val filter_map : ('a -> 'b option) -> 'a list -> 'b list
val default : 'a -> 'a option -> 'a
val get_exn : 'a t -> 'a
exception WasNone

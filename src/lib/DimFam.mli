type 'a t
val inst : 'a t -> DimVal.t -> 'a
val make : (DimVal.t -> 'a) -> 'a t
val map : ('a -> 'b) -> 'a t -> 'b t
val split : ('a * 'b) t -> 'a t * 'b t

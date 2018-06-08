type t
type 'a m = [`Ok of 'a | `Same of Dim.t * Dim.t]

val make : Dim.t -> Dim.t -> t m
val swap : t -> t
val unleash : t -> Dim.t * Dim.t
val act : Dim.action -> t -> t m

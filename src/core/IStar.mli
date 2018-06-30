type t
type 'a m = [`Ok of 'a | `Same of I.t * I.t]

val make : I.t -> I.t -> t m
val gen_const : I.atom -> [`Dim0 | `Dim1] -> t

val swap : t -> t
val unleash : t -> I.t * I.t
val act : I.action -> t -> t m

type t
type 'a m = [`Ok of 'a | `Const of [`Dim0 | `Dim1]]
val make : Dim.t -> t m
val unleash : t -> Dim.t
val act : Dim.action -> t -> t m

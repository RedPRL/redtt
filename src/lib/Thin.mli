type 'x t
type t0 = Void.t t

val id : 'x t
val keep : 'x t -> 'x t
val skip : 'x t -> 'x t
val sub : 'x t -> 'x -> 'x t
val cmp : 'x t -> 'x t -> 'x t

val act : t0 -> 'a list -> 'a list
val proj : t0 -> 'a list -> 'a


module Ix :
sig
  type 'a r = V of int | R of 'a

  val proj : ('a t -> 'a -> 'a) -> 'a t -> int -> 'a r

  val from_ix : int -> 'a t
  val to_ix : t0 -> int
end
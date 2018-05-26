module type S =
sig
  type 'a m
  val bind : 'a m -> ('a -> 'b m) -> 'b m
  val ret : 'a -> 'a m
end

module type Notation =
sig
  type 'a m

  val (>>=) : 'a m -> ('a -> 'b m) -> 'b m
  val (>>) : 'a m -> 'b m -> 'b m
  val (<@>) : ('a -> 'b) -> 'a m -> 'b m
  val (<||) : bool m -> unit m -> unit m
end

module Notation (M : S) : Notation with type 'a m := 'a M.m

module Util (M : S) :
sig
  val traverse : ('a -> 'b) -> 'a M.m list -> 'a list M.m
end


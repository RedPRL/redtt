(** Backward lists (notation inspired by Conor McBride) *)

type 'a bwd =
  | Emp
  | Snoc of 'a bwd * 'a


module BwdNotation :
sig
  val (<.>) : 'a bwd -> 'a bwd -> 'a bwd
  val (#<) : 'a bwd -> 'a -> 'a bwd
  val (<><) : 'a bwd -> 'a list -> 'a bwd
  val (<>>) : 'a bwd -> 'a list -> 'a list
end

module Bwd :
sig
  val length : 'a bwd -> int
  val map : ('a -> 'b) -> 'a bwd -> 'b bwd
  val filter : ('a -> bool) -> 'a bwd -> 'a bwd
  val to_list : 'a bwd -> 'a list
  val from_list : 'a list -> 'a bwd
end

module type S =
sig
  type state

  include Monad.S
  val get : state m
  val local : (state -> state) -> 'a m -> 'a m
  val run : state -> 'a m -> 'a
end

module M (X : sig type t end) : S with type state := X.t

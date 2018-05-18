module type S =
sig
  type state

  include Monad.S

  val get : state m
  val set : state -> unit m
end

module M (X : sig type t end) : S with type state := X.t

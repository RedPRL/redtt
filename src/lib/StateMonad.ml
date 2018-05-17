module type S =
sig
  type state

  include Monad.S

  val get : state m
  val set : state -> unit m
end

module M (X : sig type t end) : S with type state := X.t =
struct
  type state = X.t

  type 'a m = state -> 'a * state

  let ret a st = a, st

  let bind m k st =
    let a, st' = m st in
    k a st'

  let get st =
    st, st

  let set st _ =
    (), st
end

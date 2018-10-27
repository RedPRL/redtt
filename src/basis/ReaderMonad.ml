module type S =
sig
  type state

  include Monad.S
  val get : state m
  val local : (state -> state) -> 'a m -> 'a m
  val run : state -> 'a m -> 'a
end

module M (X : sig type t end) : S with type state := X.t =
struct
  type 'a m = X.t -> 'a
  let ret a _ = a

  let bind (m : 'a m) (f : 'a -> 'b m) : 'b m =
    fun st ->
      f (m st) st

  let try_ (m : 'a m) (ferr : exn -> 'a m) : 'a m =
    fun st ->
      try
        m st
      with exn ->
        ferr exn st

  let get st =
    st

  let local f m st =
    m (f st)

  let run st m =
    m st
end

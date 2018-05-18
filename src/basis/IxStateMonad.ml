module type S =
sig
  type 'i state

  include IxMonad.S

  val get : ('i, 'i, 'i state) m
  val set : 'o state -> ('i, 'o, unit) m
end

module M (X : sig type 'i t end) : S with type 'i state := 'i X.t =
struct
  type 'i state = 'i X.t

  type ('i, 'o, 'a) m = 'i state -> 'a * 'o state

  let ret a st = a, st

  let bind m k st =
    let a, st' = m st in
    k a st'

  let get st =
    st, st

  let set st _ =
    (), st
end

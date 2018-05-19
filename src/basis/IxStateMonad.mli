module type S =
sig
  type 'i state

  include IxMonad.S

  val run : 'i state -> ('i, 'o, 'a) m -> 'a * 'o state

  val get : ('i, 'i, 'i state) m
  val set : 'o state -> ('i, 'o, unit) m
end

module M (X : sig type 'i t end) : S
  with type 'i state := 'i X.t

module type S =
sig
  type t
  type 'a m
  val act : Dim.action -> t -> t m
end

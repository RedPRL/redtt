type (_, 'a) face =
  | False : IStar.t -> ('x, 'a) face
  | True : I.t * I.t * 'a -> ([`Any], 'a) face
  | Indet : IStar.t * 'a -> ('x, 'a) face

val map : (I.t -> I.t -> 'a -> 'b) -> ('x, 'a) face -> ('x, 'b) face

val forall : I.atom -> ('x, 'a) face -> [`Delete | `Keep]

module M (X : Sort.S with type 'a m = 'a) :
sig
  type 'x t = ('x, X.t) face

  val rigid : IStar.t -> (unit -> X.t) -> ('x, X.t) face

  val make : I.t -> I.t -> (unit -> X.t) -> ([`Any], X.t) face

  (* convenience function for generating rigid faces x = ε *)
  val gen_const : I.atom -> [`Dim0 | `Dim1] -> X.t -> ('x, X.t) face

  val act : I.action -> ('x, X.t) face -> [`Any] t
end

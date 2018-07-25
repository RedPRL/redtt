type (_, 'a) face =
  | False : I.t * I.t -> ([`Any], 'a) face
  | True : I.t * I.t * 'a -> ([`Any], 'a) face
  | Indet : Eq.t * 'a -> ('x, 'a) face

val map : (I.t -> I.t -> 'a -> 'b) -> ('x, 'a) face -> ('x, 'b) face

val forall : I.atom -> ('x, 'a) face -> [`Delete | `Keep]

module type S =
sig
  type body
  type 'x t = ('x, body) face

  val rigid : I.action -> Eq.t -> (I.action -> body) -> 'x t

  val make_from_dir : I.action -> Dir.t -> (I.action -> body) -> [`Any] t

  val make : I.action -> I.t -> I.t -> (I.action -> body) -> [`Any] t

  (* convenience function for generating faces x = ε *)
  val gen_const : I.action -> I.atom -> [`Dim0 | `Dim1] -> (I.action -> body) -> [`Any] t

  val act : I.action -> 'x t -> [`Any] t
end

module M (X : Sort.S with type 'a m = 'a) : S with type body := X.t

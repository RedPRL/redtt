type (_, 'a) face =
  | False : DimStar.t -> ('x, 'a) face
  | True : Dim.t * Dim.t * 'a -> ([`Any], 'a) face
  | Indet : DimStar.t * 'a -> ('x, 'a) face

module M (X : Sort.S with type 'a m = 'a) :
sig
  type 'x t = ('x, X.t) face
  val act : Dim.action -> 'x t -> [`Any] t
end =
struct
  type 'x t = ('x, X.t) face

  let act : type x. Dim.action -> x t -> _ t =
    fun phi face ->
      match face with
      | True (c, d, t) ->
        True (Dim.act phi c, Dim.act phi d, X.act phi t)
      | False p ->
        False p
      | Indet (p, t) ->
        let t' = X.act phi t in
        match DimStar.act phi p with
        | `Ok p' ->
          Indet (p', t')
        | `Same (c, d) ->
          True (c, d, t')
end

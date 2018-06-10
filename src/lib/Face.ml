type (_, 'a) face =
  | False : DimStar.t -> ('x, 'a) face
  | True : Dim.t * Dim.t * 'a -> ([`Any], 'a) face
  | Indet : DimStar.t * 'a -> ('x, 'a) face

let map : type x. (Dim.t -> Dim.t -> 'a -> 'b) -> (x, 'a) face -> (x, 'b) face =
  fun f face ->
    match face with
    | False p ->
      False p
    | True (r, r', v) ->
      True (r, r', f r r' v)
    | Indet (p, v) ->
      let r, r' = DimStar.unleash p in
      Indet (p, f r r' v)

let get_cond : type x. (x, 'a) face -> Dim.t * Dim.t =
  fun face ->
    match face with
    | False p ->
      DimStar.unleash p
    | True (r, r', _) ->
      r, r'
    | Indet (p, _) ->
      DimStar.unleash p

let forall : type x. Dim.atom -> (x, 'a) face -> [`Delete | `Keep] =
  fun x face ->
    let s = Dim.named x in
    let r, r' = get_cond face in
    if r = s or r' = s then `Delete else `Keep

module M (X : Sort.S with type 'a m = 'a) :
sig
  type 'x t = ('x, X.t) face
  val act : Dim.action -> 'x t -> [`Any] t
  val rigid : DimStar.t -> X.t -> ('x, X.t) face
  val gen_const : DimGeneric.t -> [`Dim0 | `Dim1] -> X.t -> ('x, X.t) face
  val make : Dim.t -> Dim.t -> X.t -> ([`Any], X.t) face
end =
struct
  type 'x t = ('x, X.t) face

  let rigid : type x. DimStar.t -> X.t -> (x, X.t) face =
    fun eq a ->
      let r, r' = DimStar.unleash eq in
      match Dim.compare r r' with
      | Dim.Apart ->
        False eq
      | _ ->
        Indet (eq, X.act (Dim.equate r r') a)

  let make : Dim.t -> Dim.t -> X.t -> ([`Any], X.t) face =
    fun r r' a ->
      match DimStar.make r r' with
      | `Ok p ->
        rigid p a
      | `Same _ ->
        True (r, r', a)

  let gen_const : type x. DimGeneric.t -> [`Dim0 | `Dim1] -> X.t -> (x, X.t) face =
    fun x eps a ->
      match DimStar.gen_const x eps with
      | `Ok p ->
        rigid p a
      | `Same _ ->
        failwith "Impossible"


  let act : type x. Dim.action -> x t -> _ t =
    fun phi face ->
      match face with
      | True (c, d, t) ->
        True (Dim.act phi c, Dim.act phi d, X.act phi t)
      | False p ->
        False p
      | Indet (p, t) ->
        let r, r' = DimStar.unleash p in
        let t' = X.act (Dim.cmp (Dim.equate r r') phi) t in
        match DimStar.act phi p with
        | `Ok p' ->
          Indet (p', t')
        | `Same (c, d) ->
          True (c, d, t')
end

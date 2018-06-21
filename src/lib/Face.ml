type (_, 'a) face =
  | False : IStar.t -> ('x, 'a) face
  | True : I.t * I.t * 'a -> ([`Any], 'a) face
  | Indet : IStar.t * 'a -> ('x, 'a) face

let map : type x. (I.t -> I.t -> 'a -> 'b) -> (x, 'a) face -> (x, 'b) face =
  fun f face ->
    match face with
    | False p ->
      False p
    | True (r, r', v) ->
      True (r, r', f r r' v)
    | Indet (p, v) ->
      let r, r' = IStar.unleash p in
      Indet (p, f r r' v)

let get_cond : type x. (x, 'a) face -> I.t * I.t =
  fun face ->
    match face with
    | False p ->
      IStar.unleash p
    | True (r, r', _) ->
      r, r'
    | Indet (p, _) ->
      IStar.unleash p

let forall : type x. I.atom -> (x, 'a) face -> [`Delete | `Keep] =
  fun x face ->
    let s = `Atom x in
    let r, r' = get_cond face in
    if r = s or r' = s then `Delete else `Keep

module M (X : Sort.S with type 'a m = 'a) :
sig
  type 'x t = ('x, X.t) face
  val act : I.action -> 'x t -> [`Any] t
  val rigid : IStar.t -> X.t -> ('x, X.t) face
  val gen_const : I.atom -> [`Dim0 | `Dim1] -> X.t -> ('x, X.t) face
  val make : I.t -> I.t -> X.t -> ([`Any], X.t) face
end =
struct
  type 'x t = ('x, X.t) face

  let rigid : type x. IStar.t -> X.t -> (x, X.t) face =
    fun eq a ->
      let r, r' = IStar.unleash eq in
      match I.compare r r' with
      | `Apart ->
        False eq
      | _ ->
        Indet (eq, X.act (I.equate r r') a)

  let make : I.t -> I.t -> X.t -> ([`Any], X.t) face =
    fun r r' a ->
      match IStar.make r r' with
      | `Ok p ->
        rigid p a
      | `Same _ ->
        True (r, r', a)

  let gen_const : type x. I.atom -> [`Dim0 | `Dim1] -> X.t -> (x, X.t) face =
    fun x eps a ->
      rigid (IStar.gen_const x eps) a


  let act : type x. I.action -> x t -> _ t =
    fun phi face ->
      match face with
      | True (c, d, t) ->
        True (I.act phi c, I.act phi d, X.act phi t)
      | False p ->
        begin
          match IStar.act phi p with
          | `Ok p' -> False p'
          | _ -> failwith "Unexpected thing happened in Face.act"
        end
      | Indet (p, t) ->
        begin
          match IStar.act phi p with
          | `Same (c, d) ->
            let t' = X.act phi t in
            True (c, d, t')
          | `Ok p' ->
            let r, r' = IStar.unleash p' in
            match I.compare r r' with
            | `Apart ->
              False p'
            | _ ->
              let t' = X.act (I.cmp (I.equate r r') phi) t in
              Indet (p', t')
        end
end


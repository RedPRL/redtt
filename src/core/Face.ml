type (_, 'a) face =
  | False : I.t * I.t -> ([`Any], 'a) face
  | True : I.t * I.t * 'a lazy_t -> ([`Any], 'a) face
  | Indet : Eq.t * 'a lazy_t -> ('x, 'a) face

let map : type x. (I.t -> I.t -> 'a -> 'b) -> (x, 'a) face -> (x, 'b) face =
  fun f face ->
    match face with
    | False (r, r') ->
      False (r, r')
    | True (r, r', v) ->
      True (r, r', lazy (f r r' (Lazy.force v)))
    | Indet (p, v) ->
      let r, r' = Eq.unleash p in
      Indet (p, lazy (f r r' (Lazy.force v)))

let get_cond : type x. (x, 'a) face -> I.t * I.t =
  fun face ->
    match face with
    | False (r, r') ->
      r, r'
    | True (r, r', _) ->
      r, r'
    | Indet (p, _) ->
      Eq.unleash p

let forall : type x. I.atom -> (x, 'a) face -> [`Delete | `Keep] =
  fun x face ->
    let r, r' = get_cond face in
    if I.absent x r && I.absent x r' then `Keep else `Delete

module type S =
sig
  type body
  type 'x t = ('x, body) face

  val rigid : I.action -> Eq.t -> (I.action -> body) -> 'x t

  val make_from_dir : I.action -> Dir.t -> (I.action -> body) -> [`Any] t

  val make : I.action -> I.t -> I.t -> (I.action -> body) -> [`Any] t

  (* convenience function for generating faces x = ε *)
  val gen_const : I.action -> I.atom -> [`Dim0 | `Dim1] -> (I.action -> body) -> 'a t

  val act : I.action -> 'x t -> [`Any] t
end


module M (X : Sort.S with type 'a m = 'a) : S with type body := X.t =
struct
  type 'x t = ('x, X.t) face

  let rigid : I.action -> Eq.t -> (I.action -> X.t) -> 'x t =
    fun phi eq a ->
      let r, r' = Eq.unleash eq in
      Indet (eq, lazy begin a (I.cmp (I.equate r r') phi) end)

  let make : I.action -> I.t -> I.t -> (I.action -> X.t) -> [`Any] t =
    fun phi r r' a ->
      match Eq.make r r' with
      | `Ok p ->
        rigid phi p a
      | `Apart _ ->
        False (r, r')
      | `Same _ ->
        True (r, r', lazy begin a phi end)

  let make_from_dir : I.action -> Dir.t -> (I.action -> X.t) -> [`Any] t =
    fun phi dir a ->
      match Eq.from_dir dir with
      | `Ok p ->
        rigid phi p a
      | `Apart (r, r') ->
        False (r, r')

  let gen_const : I.action -> I.atom -> [`Dim0 | `Dim1] -> (I.action -> X.t) -> 'x t =
    fun phi x eps a ->
      rigid phi (Eq.gen_const x eps) a


  let act : type x. I.action -> x t -> _ t =
    fun phi face ->
      match face with
      | True (c, d, t) ->
        True (I.act phi c, I.act phi d, lazy begin X.act phi @@ Lazy.force t end)
      | False (r, r') ->
        begin
          match Eq.make (I.act phi r) (I.act phi r') with
          | `Apart (r, r') -> False (r, r')
          | _ -> failwith "Unexpected thing happened in Face.act"
        end
      | Indet (p, t) ->
        begin
          match Eq.act phi p with
          | `Same (c, d) ->
            let t' = lazy begin X.act phi @@ Lazy.force t end in
            True (c, d, t')
          | `Apart (c, d) ->
            False (c, d)
          | `Ok p' ->
            rigid phi p' (fun phi -> X.act phi @@ Lazy.force t)
        end
end


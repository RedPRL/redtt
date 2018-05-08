module D = Dim

type t = D.t * D.t
type 'a m = [`Ok of 'a | `Same of t]

let make c d =
  match D.compare c d with
  | D.Same ->
    `Same (c, d)
  | _ ->
    `Ok (c, d)

let unleash p = p

let act phi (r, r') =
  make (D.act phi r) (D.act phi r')

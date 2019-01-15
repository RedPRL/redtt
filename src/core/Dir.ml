type t = I.t * I.t

type 'a m = [`Ok of 'a | `Same of t]

let make r r' =
  if r = r' then `Same (r, r') else `Ok (r, r')

let gen_const x epsilon : t =
  `Atom x,
  match epsilon with
  | `Dim0 -> `Dim0
  | `Dim1 -> `Dim1

let swap (r, r') = r', r
let unleash p = p

let act phi (r, r') : t m =
  make (I.act phi r) (I.act phi r')

let pp fmt (r, r') =
  Format.fprintf fmt "%a ~> %a" I.pp r I.pp r'

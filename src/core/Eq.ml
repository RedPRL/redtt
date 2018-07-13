type t = I.t * I.t

type 'a m = [`Ok of 'a | `Same of t | `Apart of t]

let make r r' =
  match I.compare r r' with
  | `Same -> `Same (r, r')
  | `Apart -> `Apart (r, r')
  | `Indet -> `Ok (r, r')

let gen_const x epsilon : t =
  `Atom x,
  match epsilon with
  | `Dim0 -> `Dim0
  | `Dim1 -> `Dim1

let from_dir dir =
  let r, r' = Dir.unleash dir in
  match I.compare r r' with
  | `Apart -> `Apart (r, r')
  | `Indet -> `Ok (r, r')
  | `Same -> failwith "impossible"

let swap (r, r') = r', r
let unleash p = p

let act phi (r, r') : t m =
  make (I.act phi r) (I.act phi r')

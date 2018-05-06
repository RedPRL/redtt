module D = DimVal
type dim = D.t
type atom = Symbol.t

type t =
  | Swap of atom * atom
  | Cmp of t * t
  | Id

let emp = Id

let swap a b = Swap (a, b)
let cmp f g = Cmp (f, g)

let rec lookup x pi =
  match pi with
  | Id -> x
  | Swap (a, b) ->
    if x = a then
      b
    else if x = b then
      a
    else
      x
  | Cmp (pi, pi') ->
    let x' = lookup x pi' in
    lookup x' pi

let read r pi =
  match r with
  | D.Named x ->
    D.Named (lookup x pi)
  | _ -> r

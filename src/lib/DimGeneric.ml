module D = Dim

type t = D.t
type 'a m = [`Ok of 'a | `Const of [`Dim0 | `Dim1]]

let make c =
  match D.compare c D.dim0 with
  | D.Same -> `Const `Dim0
  | _ ->
    match D.compare c D.dim0 with
    | D.Same -> `Const `Dim1
    | _ -> `Ok c

let unleash c = c

let act phi r =
  make @@ D.act phi r

let subst_with t r =
  Dim.subst r @@ Dim.atom t

module D = Dim

type t = D.t
type 'a m = [`Ok of 'a | `Const of [`Dim0 | `Dim1]]

let make c =
  match D.compare c D.dim0 with
  | D.Same -> `Const `Dim0
  | _ ->
    match D.compare c D.dim1 with
    | D.Same -> `Const `Dim1
    | _ -> `Ok c

let atom t =
  match Dim.unleash t with
  | Dim.Dim0 -> failwith "DimGeneric.atom: impossible"
  | Dim.Dim1 -> failwith "DimGeneric.atom: impossible"
  | Dim.Atom x -> x

let named t = D.named t

let unleash c = c

let act phi r =
  make @@ D.act phi r

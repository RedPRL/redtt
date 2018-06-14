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

let name t =
  match Dim.unleash t with
  | Dim.Dim0 -> failwith "DimGeneric.name: impossible"
  | Dim.Dim1 -> failwith "DimGeneric.name: impossible"
  | Dim.Atom x -> x

let unleash c = c

let act phi r =
  make @@ D.act phi r

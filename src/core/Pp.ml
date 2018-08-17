open RedBasis open Bwd open BwdNotation

module Env =
struct
  type t = int * string bwd

  let emp = 0, Emp
  let var i (_, xs) =
    try
      Bwd.nth xs i ^ "{" ^ string_of_int i ^ "}"
    with
    | _ ->
      "{" ^ string_of_int i ^ "}"
  (* failwith "Pp printer: tried to resolve bound variable out of range" *)

  let bind_fresh (i, xs) =
    let x = "x" ^ string_of_int i in
    x, (i + 1, xs #< x)

  let proj (i, xs) =
    match xs with
    | Emp -> failwith "ppenv/proj"
    | Snoc (xs, _) -> (i - 1, xs)

  let bind (i, xs) nm =
    match nm with
    | None ->
      let x = "x" ^ string_of_int i in
      x, (i + 1, xs #< x)
    | Some x ->
      x, (i, xs #< x)

  let bindn ((n, xs) : t) (nms : string option list) =
    let xs' = List.mapi (fun i nm -> match nm with Some x -> x | None -> "x" ^ string_of_int (n + i)) nms in
    xs', (n + List.length nms, xs <>< xs')
end

type env = Env.t


type 'a t0 = Format.formatter -> 'a -> unit
type 'a t = env -> 'a t0

let pp_list pp fmt xs =
  let pp_sep fmt () = Format.fprintf fmt ", " in
  Format.fprintf fmt "@[<hv1>[%a]@]"
    (Format.pp_print_list ~pp_sep pp) xs

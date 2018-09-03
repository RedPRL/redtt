open RedBasis open Bwd open BwdNotation

module Env =
struct
  type t = int * string bwd

  let emp = 0, Emp
  let var i (_, xs) =
    try
      Bwd.nth xs i
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

  let choose_name (i, xs) nm =
    match nm with
    | None | Some "_" ->
      let x = "x" ^ string_of_int i in
      x
    | Some x ->
      let ys = Bwd.filter (fun y -> y = x) xs in
      let n = Bwd.length ys in
      if n = 0 then
        x
      else
        x ^ string_of_int n

  let bind (i, xs) nm =
    let x = choose_name (i, xs) nm in
    x, (i + 1, xs #< x)

  let rec bindn env (nms : string option list) =
    match nms with
    | [] ->
      [], env
    | nm :: nms ->
      let x, env' = bind env nm in
      let xs, env'' = bindn env' nms in
      (x :: xs), env''
end

type env = Env.t


type 'a t0 = Format.formatter -> 'a -> unit
type 'a t = env -> 'a t0

let pp_list pp fmt xs =
  let pp_sep fmt () = Format.fprintf fmt ", " in
  Format.fprintf fmt "@[<hv1>[%a]@]"
    (Format.pp_print_list ~pp_sep pp) xs

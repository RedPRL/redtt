open RedBasis open Bwd open BwdNotation

module Env =
struct
  type t = string bwd

  let emp = Emp

  let var i xs =
    try
      Bwd.nth xs i
    with
    | _ ->
      "{" ^ string_of_int i ^ "}"
  (* failwith "Pp printer: tried to resolve bound variable out of range" *)

  let proj xs =
    match xs with
    | Emp -> failwith "ppenv/proj"
    | Snoc (xs, _) -> xs

  let choose_name xs x =
    match x with
    | _ ->
      let ys = Bwd.filter (fun y -> y = x) xs in
      let n = Bwd.length ys in
      if n = 0 then
        x
      else
        x ^ string_of_int n

  let bind xs nm =
    let x =
      match nm with
      | None | Some "_" -> choose_name xs "x"
      | Some x -> choose_name xs x
    in
    x, xs #< x

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

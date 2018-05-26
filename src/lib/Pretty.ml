module Env =
struct
  type t = int * string list

  let emp = 0, []
  let var i (_, xs) = List.nth xs i
  let bind_fresh (i, xs) =
    let x = "x" ^ string_of_int i in
    x, (i + 1, x :: xs)

  let proj (i, xs) =
    match xs with
    | [] -> failwith "ppenv/proj"
    | _::xs -> (i, xs)

  let bind nm (i, xs) =
    match nm with
    | None ->
      let x = "x" ^ string_of_int i in
      x, (i + 1, x :: xs)
    | Some x ->
      x, (i, x:: xs)

  let rec bindn nms t =
    match nms with
    | [] -> [], t
    | nm :: nms ->
      let x, t = bind nm t in
      let xs, t = bindn nms t in
      x :: xs, t
end

type env = Env.t


type 'a t0 = Format.formatter -> 'a -> unit
type 'a t = env -> 'a t0

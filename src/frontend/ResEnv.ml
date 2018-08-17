open RedBasis
open RedTT_Core
open Bwd open BwdNotation

module T = PersistentTable.M
type t = string option bwd * (string, Name.t) T.t

let init () = Emp, T.init ~size:30
let bind x (env, tbl) = env #< (Some x), tbl

(* TODO: is this backwards? *)
let bindn xs (env, tbl) = env <>< List.map (fun x -> Some x) xs, tbl

let bind_opt x (env, tbl) = env #< x, tbl

let rec get x (env, tbl) =
  let rec go env =
    match env with
    | Emp ->
      failwith @@ "variable not found: " ^ x
    | Snoc (ys, Some y) ->
      if x = y
      then 0
      else 1 + go ys
    | Snoc (ys, None) ->
      1 + go ys
  in
  try
    `Ix (go env)
  with
  | _ ->
    match T.find x tbl with
    | Some r -> `Var r
    | None -> failwith @@ "Could not resolve variable: " ^ x



let global s x (env, tbl) =
  env, T.set s x tbl

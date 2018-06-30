open RedBasis
open RedTT_Core

module T = PersistentTable.M
type t = string option list * (string, Name.t) T.t

let init () = [], T.init ~size:30
let bind x (env, tbl) = Some x :: env, tbl

(* TODO: is this backwards? *)
let bindn xs (env, tbl) = List.map (fun x -> Some x) xs @ env, tbl

let bind_opt x (env, tbl) = x :: env, tbl

let rec get x (env, tbl) =
  let rec go env =
    match env with
    | [] ->
      failwith @@ "variable not found: " ^ x
    | Some y :: ys ->
      if x = y
      then 0
      else 1 + go ys
    | None :: ys ->
      1 + go ys
  in
  try
    `Ix (go env )
  with
  | _ ->
    match T.find x tbl with
    | Some r -> `Ref r
    | None -> failwith @@ "Could not resolve variable: " ^ x



let global s x (env, tbl) =
  env, T.set s x tbl

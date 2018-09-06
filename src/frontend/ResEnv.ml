open RedBasis
open RedTT_Core
open Bwd open BwdNotation

type resolution =
  [ `Ix of int
  | `Var of Name.t
  ]


module T = PersistentTable.M

type t =
  {locals : string option bwd;
   globals : (string, Name.t) T.t}

let init () =
  {locals = Emp;
   globals = T.init ~size:30}

let bind x renv =
  {renv with
   locals = renv.locals #< (Some x)}

(* TODO: is this backwards? *)
let bindn xs renv =
  {renv with
   locals = renv.locals <>< List.map (fun x -> Some x) xs}

let bind_opt x renv =
  {renv with locals = renv.locals #< x}

let rec get x renv =
  let rec go ys acc =
    match ys with
    | Emp ->
      failwith @@ "variable not found: " ^ x
    | Snoc (ys, Some y) ->
      if x = y
      then acc
      else go ys (acc + 1)
    | Snoc (ys, None) ->
      (go[@tailcall]) ys (acc + 1)
  in
  try
    `Ix (go renv.locals 0)
  with
  | _ ->
    match T.find x renv.globals with
    | Some r ->
      `Var r
    | None ->
      failwith @@ "Could not resolve variable: " ^ x



let global s x renv =
  {renv with
   globals = T.set s x renv.globals}

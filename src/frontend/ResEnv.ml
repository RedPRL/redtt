open RedBasis
open Bwd open BwdNotation
open RedTT_Core

type global =
  [ `Var of Name.t
  | `Metavar of Name.t
  | `Datatype of string
  ]

type resolution =
  [ `Ix of int
  | `Var of Name.t
  | `Metavar of Name.t
  | `Datatype of string
  ]


module T = PersistentTable.M

type t =
  {locals : string option bwd;
   globals : (string, global) T.t}

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

let get x renv =
  let rec go ys acc =
    match ys with
    | Emp ->
      failwith @@ "variable not found: " ^ x
    | Snoc (ys, Some y) ->
      if x = y
      then acc
      else (go[@tailcall]) ys (acc + 1)
    | Snoc (ys, None) ->
      (go[@tailcall]) ys (acc + 1)
  in
  try
    `Ix (go renv.locals 0)
  with
  | _ ->
    match T.find x renv.globals with
    | Some (`Var x) ->
      `Var x
    | Some (`Metavar x) ->
      `Metavar x
    | Some (`Datatype x) ->
      `Datatype x
    | None ->
      failwith @@ "Could not resolve variable: " ^ x



let named_var s x renv =
  {renv with
   globals = T.set s (`Var x) renv.globals}

let named_metavar s x renv =
  {renv with
   globals = T.set s (`Metavar x) renv.globals}

let datatype s renv =
  {renv with
   globals = T.set s (`Datatype s) renv.globals}

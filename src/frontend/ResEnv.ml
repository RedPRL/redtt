open RedBasis
open Bwd open BwdNotation
open RedTT_Core

type global =
  [ `Var of Name.t
  | `Metavar of Name.t
  | `Datatype of Name.t
  ]

type resolution =
  [ `Ix of int
  | `Var of Name.t
  | `Metavar of Name.t
  | `Datatype of Name.t
  ]

type visibility =
  [ `Private | `Public ]


module T = PersistentTable.M

type t =
  {locals : string option bwd;
   globals : (string, global * visibility) T.t}

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
    | Some (`Var x, _) ->
      `Var x
    | Some (`Metavar x, _) ->
      `Metavar x
    | Some (`Datatype x, _) ->
      `Datatype x
    | None ->
      failwith @@ "Could not resolve variable: " ^ x


let set_global_ s x renv =
  {renv with
   globals = T.set s x renv.globals}

let set_global nm x renv =
  match Name.name nm with
  | Some str -> set_global_ str x renv
  | None -> renv

let register_var ~visibility nm =
  set_global nm (`Var nm, visibility)

let register_metavar ~visibility nm =
  set_global nm (`Metavar nm, visibility)

let register_datatype ~visibility nm =
  set_global nm (`Datatype nm, visibility)

let import_globals ~visibility imported renv =
  {renv with
   globals =
     let merger s (x, vis) globals =
       match vis with
       | `Private -> globals
       | `Public ->
         T.set s (x, visibility) globals
     in
     T.fold merger imported.globals renv.globals}

let pp_visibility fmt =
  function
  | `Public -> Format.fprintf fmt "public"
  | `Private -> Format.fprintf fmt "private"

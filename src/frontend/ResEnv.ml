open RedBasis
open Bwd open BwdNotation
open RedTT_Core

type global =
  [ `Name of Name.t
  | `Datatype of Name.t
  ]

type resolution =
  [ `Ix of int
  | `Name of Name.t
  | `Datatype of Name.t
  ]

type visibility =
  [ `Private | `Public ]


module T = PersistentTable.M

type global_info = global * visibility

(** the [id] here is only assigned to natives. it is important not to
    assign anything to the imported stuff. *)
type globals =
  {info_of_string : (string, [`Id of int | `Imported of global_info]) T.t;
   string_of_id : (int, string) T.t;
   info_of_id : (int, global_info) T.t;
   id_of_name : (Name.t, int) T.t}

type t =
  {locals : string option bwd;
   globals : globals}

let init_globals () =
  let size = 30 in
  {info_of_string = T.init ~size;
   string_of_id = T.init ~size;
   info_of_id = T.init ~size;
   id_of_name = T.init ~size}

let init () =
  {locals = Emp;
   globals = init_globals ()}

let modify_globals f renv =
  {renv with globals = f renv.globals}

let bind x renv =
  {renv with
   locals = renv.locals #< (Some x)}

(* TODO: is this backwards? *)
let bindn xs renv =
  {renv with
   locals = renv.locals <>< List.map (fun x -> Some x) xs}

let bind_opt x renv =
  {renv with locals = renv.locals #< x}

let info_of_string_ s renv =
  T.find s renv.globals.info_of_string

let string_of_id id renv =
  T.find id renv.globals.string_of_id

let id_of_name name renv =
  T.find name renv.globals.id_of_name

let info_of_id i renv =
  T.find i renv.globals.info_of_id

let info_of_string s renv =
  Option.foreach (info_of_string_ s renv) @@
  function
  | `Imported info -> info
  | `Id i ->
    match info_of_id i renv with
    | None ->
      Format.eprintf "Invariant in ResEnv is broken; id %i escapes the info context." i;
      raise Not_found
    | Some info -> info

let get x renv =
  let rec go ys acc =
    match ys with
    | Emp ->
      raise Not_found
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
  | Not_found ->
    match info_of_string x renv with
    | Some (`Name x, _) ->
      `Name x
    | Some (`Datatype x, _) ->
      `Datatype x
    | None ->
      failwith @@ "Could not resolve variable: " ^ x

let get_name x renv =
  match get x renv with
  | `Name x -> x
  | _ -> failwith "ResEnv.get_name: expected to find name"

let register_global name info renv =
  renv |> modify_globals @@ fun globals ->
  let id, info_of_id, id_of_name =
    match id_of_name name renv with
    | Some id -> id, globals.info_of_id, globals.id_of_name
    | None ->
      let id = T.size globals.info_of_id in
      id,
      T.set id info globals.info_of_id,
      T.set name id globals.id_of_name
  in
  let info_of_string, string_of_id =
    match Name.name name with
    | None -> globals.info_of_string, globals.string_of_id
    | Some s ->
      match info_of_string_ s renv with
      | None | Some (`Imported _) ->
        T.set s (`Id id) globals.info_of_string,
        T.set id s globals.string_of_id
      | Some (`Id old_id) when old_id = id ->
        globals.info_of_string,
        globals.string_of_id
      | Some (`Id old_id) ->
        T.set s (`Id id) globals.info_of_string,
        T.set id s @@ T.remove old_id globals.string_of_id
  in
  {info_of_id; id_of_name; info_of_string; string_of_id}

let import_global s info renv =
  renv |> modify_globals @@ fun globals ->
  let info_of_string, string_of_id =
    match info_of_string_ s renv with
    | None | Some (`Imported _) ->
      T.set s (`Imported info) globals.info_of_string,
      globals.string_of_id
    | Some (`Id id) ->
      T.set s (`Imported info) globals.info_of_string,
      T.remove id globals.string_of_id
  in
  {globals with info_of_string; string_of_id}

let register_var ~visibility nm =
  register_global nm (`Name nm, visibility)

let register_datatype ~visibility nm =
  register_global nm (`Datatype nm, visibility)

let import_globals ~visibility imported renv =
  let merger s id_or_imported renv =
    let info =
      match id_or_imported with
      | `Imported info -> info
      | `Id id ->
        match info_of_id id imported with
        | None ->
          Format.eprintf "Invariant in ResEnv is broken; id %i escapes the info context." id;
          raise Not_found
        | Some info -> info
    in
    match info with
    | _, `Private -> renv
    | global, `Public ->
      import_global s (global, visibility) renv
  in
  T.fold merger imported.globals.info_of_string renv

let name_of_global =
  function
  | `Name nm | `Datatype nm -> nm

let export_native_globals renv : (string option * Name.t) list =
  let f (id, (global, vis)) =
    let ostr = match vis with `Private -> None | `Public -> string_of_id id renv in
    ostr, name_of_global global
  in
  List.sort compare @@ List.of_seq @@ Seq.map f @@ T.to_seq renv.globals.info_of_id

let pp_visibility fmt =
  function
  | `Public -> Format.fprintf fmt "public"
  | `Private -> Format.fprintf fmt "private"

open RedBasis
open Bwd open BwdNotation
open RedTT_Core

type resolution =
  [ `Ix of int
  | `Name of Name.t
  ]

type visibility =
  [ `Private | `Public ]


module T = PersistentTable.M

type global_info = Name.t * visibility

(** the [native] here is only assigned to natives. it is important not to
    assign anything to the imported stuff. *)
type globals =
  {info_of_string : (string, [`Native of int | `Imported of global_info]) T.t;
   string_of_native : (int, string) T.t;
   info_of_native : (int, global_info) T.t;
   native_of_name : (Name.t, int) T.t}

type t =
  {locals : string option bwd;
   globals : globals}

let init_globals () =
  let size = 30 in
  {info_of_string = T.init ~size;
   string_of_native = T.init ~size;
   info_of_native = T.init ~size;
   native_of_name = T.init ~size}

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

let string_of_native native renv =
  T.find native renv.globals.string_of_native

let native_of_name name renv =
  T.find name renv.globals.native_of_name

let info_of_native i renv =
  T.find i renv.globals.info_of_native

let info_of_string s renv =
  Option.foreach (info_of_string_ s renv) @@
  function
  | `Imported info -> info
  | `Native i ->
    match info_of_native i renv with
    | None ->
      Format.eprintf "Invariant in ResEnv is broken; native %i escapes the info context." i;
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
    | Some (x, _) ->
      `Name x
    | None ->
      failwith @@ "Could not resolve variable: " ^ x

let get_name x renv =
  match get x renv with
  | `Name x -> x
  | _ -> failwith "ResEnv.get_name: expected to find name"

let add_native_global_ os ((name, visibility) as info) renv =
  renv |> modify_globals @@ fun globals ->
  let native, info_of_native, native_of_name =
    match native_of_name name renv with
    | Some native ->
      (* should be idempotent *)
      native, globals.info_of_native, globals.native_of_name
    | None ->
      let native = T.size globals.info_of_native in
      native,
      T.set native (name, visibility) globals.info_of_native,
      T.set name native globals.native_of_name
  in
  let info_of_string, string_of_native =
    match os with
    | None -> globals.info_of_string, globals.string_of_native
    | Some s ->
      match info_of_string_ s renv with
      | None | Some (`Imported _) ->
        T.set s (`Native native) globals.info_of_string,
        T.set native s globals.string_of_native
      | Some (`Native old_native) when old_native = native ->
        globals.info_of_string,
        globals.string_of_native
      | Some (`Native old_native) ->
        T.set s (`Native native) globals.info_of_string,
        T.set native s @@ T.remove old_native globals.string_of_native
  in
  {info_of_native; native_of_name; info_of_string; string_of_native}

let add_native_global ~visibility name =
  add_native_global_ (Name.name name) (name, visibility)

let import_global s info renv =
  renv |> modify_globals @@ fun globals ->
  let info_of_string, string_of_native =
    match info_of_string_ s renv with
    | None | Some (`Imported _) ->
      T.set s (`Imported info) globals.info_of_string,
      globals.string_of_native
    | Some (`Native native) ->
      T.set s (`Imported info) globals.info_of_string,
      T.remove native globals.string_of_native
  in
  {globals with info_of_string; string_of_native}

let import_globals ~visibility imported renv =
  let merger s native_or_imported renv =
    let info =
      match native_or_imported with
      | `Imported info -> info
      | `Native native ->
        match info_of_native native imported with
        | None ->
          Format.eprintf "Invariant in ResEnv is broken; native %i escapes the info context." native;
          raise Not_found
        | Some info -> info
    in
    match info with
    | _, `Private -> renv
    | name, `Public ->
      import_global s (name, visibility) renv
  in
  T.fold merger imported.globals.info_of_string renv

let name_of_native i renv =
  Option.map (fun (name, _) -> name) @@
  info_of_native i renv

type exported_natives = (string option * Name.t) list
type exported_foreigners = (string * Name.t) list

let export_native_globals renv : (string option * Name.t) list =
  let f (native, (name, vis)) =
    let ostr = match vis with `Private -> None | `Public -> string_of_native native renv in
    ostr, name
  in
  List.sort compare @@ List.of_seq @@ Seq.map f @@ T.to_seq renv.globals.info_of_native

let export_foreign_globals renv : (string * Name.t) list =
  let f (s, native_or_imported) =
    match native_or_imported with
    | `Imported (name, `Public) -> Some (s, name)
    | _ -> None
  in
  List.sort compare @@ List.of_seq @@ Seq.filter_map f @@ T.to_seq renv.globals.info_of_string

let reconstruct foreigners natives =
  let renv = init () in
  let renv = List.fold_left (fun renv (s, n) -> import_global s (n, `Public) renv) renv foreigners in
  let renv = List.fold_left (fun renv (os, n) -> add_native_global_ os (n, `Public) renv) renv natives in
  renv

let pp_visibility fmt =
  function
  | `Public -> Format.fprintf fmt "public"
  | `Private -> Format.fprintf fmt "private"

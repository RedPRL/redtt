open RedBasis
open Bwd open BwdNotation
open RedTT_Core

type resolution =
  [ `Ix of int
  | `Name of Name.t
  ]

type visibility =
  [ `Private | `Public ]

let pp_visibility fmt =
  function
  | `Public -> Format.fprintf fmt "public"
  | `Private -> Format.fprintf fmt "private"


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

let add_native_global ~visibility name renv =
  let info = name, visibility in
  Combinators.flip modify_globals renv @@ fun globals ->
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
    match Name.name name with
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

let import_global ~visibility name renv =
  match Name.name name with
  | None -> invalid_arg "import_global"
  | Some s ->
    let info = name, visibility in
    Combinators.flip modify_globals renv @@ fun globals ->
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

let import_public ~visibility imported renv =
  let f s =
    match info_of_string s imported with
    | Some (name, `Public) -> Some name
    | _ -> None
  in
  let names = ListUtil.filter_map f (T.to_list_keys imported.globals.info_of_string) in
  List.fold_left (fun renv name -> import_global ~visibility name renv) renv names

let name_of_native i renv =
  Option.map (fun (name, _) -> name) @@
  info_of_native i renv

type exported_natives = (string option * Name.t) list
type exported_foreigners = Name.t list

let export_native_globals renv : exported_natives =
  let f (native, (name, vis)) =
    let ostr = match vis with `Private -> None | `Public -> string_of_native native renv in
    (native, (ostr, name))
  in
  let mycompare (i0, _) (i1, _) = compare i0 i1 in
  List.map (function _, datum -> datum) @@ List.sort mycompare @@ List.map f @@ T.to_list renv.globals.info_of_native

let export_foreign_globals renv : exported_foreigners =
  let f (s, native_or_imported) =
    match native_or_imported with
    | `Imported (name, `Public) -> Some name
    | _ -> None
  in
  let compare_name n0 n1 = compare (Name.name n0) (Name.name n1) in
  List.sort compare_name @@ ListUtil.filter_map f @@ T.to_list renv.globals.info_of_string

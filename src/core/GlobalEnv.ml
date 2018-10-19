type ty = Tm.tm
type tm = Tm.tm

type entry =
  [ `P of ty
  | `Def of ty * tm
  | `Tw of ty * ty
  | `I
  | `Data of Desc.desc
  ]

module T = Map.Make (Name)

type t =
  {rel : Restriction.t;
   table : entry T.t;
   len : int}


let emp () =
  {table = T.empty;
   rel = Restriction.emp ();
   len = 0}


let declare_datatype dlbl desc (sg : t) : t =
  {sg with
   table = T.add dlbl (`Data desc) sg.table;
   len = sg.len + 1}

let replace_datatype dlbl desc (sg : t) : t =
  {sg with
   table = T.update dlbl (function Some (`Data _) -> Some (`Data desc) | _ -> raise Not_found) sg.table}

let lookup_datatype sg dlbl =
  match T.find dlbl sg.table with
  | `Data desc -> desc
  | _ ->
    Format.eprintf "The name %a does not refer to a datatype.@." Name.pp dlbl;
    raise Not_found
  | exception Not_found ->
    Format.eprintf "Datatype not found: %a.@." Name.pp dlbl;
    raise Not_found

let ext_ (sg : t) nm param : t =
  {sg with
   table = T.add nm param sg.table;
   len = sg.len + 1}


let define (sg : t) nm ~ty ~tm =
  {sg with
   table = T.add nm (`Def (ty, tm)) sg.table;
   len = sg.len + 1}

let ext (sg : t) =
  ext_ sg

let ext_meta (sg : t) =
  ext_ sg

let ext_dim (sg : t) nm : t =
  ext_ sg nm `I


let rec index_of pred xs =
  match xs with
  | [] -> failwith "index_of"
  | x :: xs ->
    if pred x then 0 else 1 + index_of pred xs

let lookup_ty sg nm tw =
  let prm = T.find nm sg.table in
  match prm, tw with
  | `P a, _ -> a
  | `Def (a, _), _ -> a
  | `Tw (a, _), `TwinL -> a
  | `Tw (_, a), `TwinR -> a
  | `Data info, _ -> Tm.univ ~kind:info.kind ~lvl:info.lvl
  | _ -> failwith "GlobalEnv.lookup_entry"

let lookup sg nm =
  T.find nm sg.table

let lookup_with_twin sg nm tw =
  let param =
    try
      lookup sg nm
    with
    | _ ->
      Format.eprintf "Failed to find: %a@." Name.pp nm;
      Printexc.print_raw_backtrace stderr (Printexc.get_callstack 20);
      Format.eprintf "@.";
      failwith "GlobalEnv.M.lookup: not found"
  in
  match param, tw with
  | `P ty, _ ->
    ty, None
  | `Def (ty, tm), _ ->
    ty, Some tm
  | `Tw (ty, _), `TwinL ->
    ty, None
  | `Tw (_, ty), `TwinR ->
    ty, None
  | _ ->
    failwith "GlobalEnv.lookup_with_twin: twin mismatch"

let restriction sg =
  sg.rel

let restrict tr0 tr1 sg =
  let ev_dim tr =
    match Tm.unleash tr with
    | Tm.Up (Tm.Var {name; _}, []) -> `Atom name
    | Tm.Dim0 -> `Dim0
    | Tm.Dim1 -> `Dim1
    | _ ->
      Printexc.print_raw_backtrace stderr (Printexc.get_callstack 20);
      Format.eprintf "@.";
      failwith "Restrict: expected dimension"
  in
  let rel', _ = Restriction.equate (ev_dim tr0) (ev_dim tr1) sg.rel in
  {sg with rel = rel'}

let pp fmt sg =
  let pp_sep fmt () = Format.fprintf fmt "; " in
  let go fmt (nm, p) =
    match p with
    | `Tw _ ->
      Format.fprintf fmt "%a[twin]"
        Name.pp nm
    | (`I | `P _ | `Def _ | `Data _) ->
      Format.fprintf fmt "%a"
        Name.pp nm
  in
  Format.pp_print_list ~pp_sep go fmt @@ T.bindings sg.table

let pp_twin fmt =
  function
  | `Only ->
    Format.fprintf fmt "Only"
  | `TwinL ->
    Format.fprintf fmt "TwinL"
  | `TwinR ->
    Format.fprintf fmt "TwinR"


let global_dims globals =
  T.fold
    (fun x prm tbl ->
       match prm with
       | `I -> T.add x (I.act (Restriction.as_action globals.rel) (`Atom x)) tbl
       | _ -> tbl)
    globals.table
    T.empty

module M (Sig : sig val globals : t end) : Val.Sig =
struct

  let restriction = Sig.globals.rel

  let global_dims = global_dims Sig.globals

  let lookup_datatype =
    lookup_datatype Sig.globals

  let lookup_with_twin =
    lookup_with_twin Sig.globals
end

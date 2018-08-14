type 'a param =
  [ `P of 'a
  | `Tw of 'a * 'a
  | `Tick
  | `I
  ]

module T = Map.Make (Name)
module StringTable = Map.Make (String)

type ty = Tm.tm
type entry = {ty : ty; sys : (Tm.tm, Tm.tm) Tm.system}
type lock_info = {constant : bool; birth : int}

type t =
  {rel : Restriction.t;
   data_decls : (Tm.tm, Tm.tm Desc.Boundary.term) Desc.desc StringTable.t;
   table : (entry param * lock_info) T.t;
   killed : int -> bool;
   under_tick : int -> bool;
   len : int}


let emp () =
  {table = T.empty;
   data_decls = StringTable.empty;
   rel = Restriction.emp ();
   killed = (fun _ -> false);
   under_tick = (fun _ -> false);
   len = 0}


let declare_datatype dlbl desc (sg : t) : t =
  {sg with
   data_decls = StringTable.add dlbl desc sg.data_decls}

let lookup_datatype dlbl sg =
  try
    StringTable.find dlbl sg.data_decls
  with
  | _ -> failwith ("Datatype not found: " ^ dlbl)

let ext_ (sg : t) ~constant nm param : t =
  let linfo = {constant; birth = sg.len} in
  {sg with
   table = T.add nm (param, linfo) sg.table;
   len = sg.len + 1}


let define (sg : t) nm ~ty ~tm =
  let face = Tm.make Tm.Dim0, Tm.make Tm.Dim0, Some tm in
  let sys = [face] in
  let linfo = {constant = true; birth = sg.len} in
  {sg with
   table = T.add nm (`P {ty; sys}, linfo) sg.table;
   len = sg.len + 1}

let ext (sg : t) =
  ext_ sg ~constant:false

let ext_meta (sg : t) =
  ext_ sg ~constant:true

let ext_tick (sg : t) nm : t =
  let sg' = ext_ sg ~constant:false nm `Tick in
  { sg' with
    under_tick = fun i -> if i <= sg.len then true else sg'.under_tick i
  }

let ext_dim (sg : t) nm : t =
  ext_ sg ~constant:false nm `I


let rec index_of pred xs =
  match xs with
  | [] -> failwith "index_of"
  | x :: xs ->
    if pred x then 0 else 1 + index_of pred xs

let kill_from_tick (sg : t) nm : t =
  try
    let _, tick_linfo = T.find nm sg.table in
    {sg with killed = fun i -> if i < sg.len && i >= tick_linfo.birth then true else sg.killed i}
  with
  | _ -> sg

let lookup_entry sg nm tw =
  let prm, linfo = T.find nm sg.table in
  let killed = sg.killed linfo.birth in
  if not linfo.constant && killed then
    failwith "GlobalEnv.lookup_entry: not accessible (modal!!)"
  else
    match prm, tw with
    | `P a, _ -> a
    | `Tw (a, _), `TwinL -> a
    | `Tw (_, a), `TwinR -> a
    | _ -> failwith "GlobalEnv.lookup_entry"

let lookup_kind sg nm =
  let prm, _ = T.find nm sg.table in
  match prm with
  | `P _ -> `P ()
  | `Tw _ -> `Tw ((), ())
  | `I -> `I
  | `Tick -> `Tick


let lookup_ty sg nm (tw : Tm.twin) =
  let {ty; _} = lookup_entry sg nm tw in
  ty

let restriction sg =
  sg.rel

let restrict tr0 tr1 sg =
  let ev_dim tr =
    match Tm.unleash tr with
    | Tm.Up (Tm.Var {name; _}, Emp) -> `Atom name
    | Tm.Dim0 -> `Dim0
    | Tm.Dim1 -> `Dim1
    | _ -> failwith "Restrict: expected dimension"
  in
  let rel', _ = Restriction.equate (ev_dim tr0) (ev_dim tr1) sg.rel in
  {sg with rel = rel'}

let pp fmt sg =
  let pp_sep fmt () = Format.fprintf fmt "; " in
  let go fmt (nm, (p, _)) =
    match p with
    | `Tw _ ->
      Format.fprintf fmt "%a[twin]"
        Name.pp nm
    | (`Tick | `I | `P _ | `Def _) ->
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

module M (Sig : sig val globals : t end) : Val.Sig =
struct

  let restriction = Sig.globals.rel

  let global_dim x =
    let phi = Restriction.as_action restriction in
    let r = I.act phi @@ `Atom x in
    (* Format.eprintf "[%a] != %a ==> %a@." Restriction.pp restriction Name.pp x I.pp r; *)
    r

  let lookup_datatype lbl =
    lookup_datatype lbl Sig.globals

  let lookup nm tw =
    let param, _ =
      try
        T.find nm Sig.globals.table
      with
      | _ ->
        Format.eprintf "Failed to find: %a@." Name.pp nm;
        Printexc.print_raw_backtrace stderr (Printexc.get_callstack 20);
        Format.eprintf "@.";
        failwith "GlobalEnv.M.lookup: not found"
    in
    match param, tw with
    | `P entry, _ ->
      entry.ty, entry.sys
    | `Tw (entry, _), `TwinL ->
      entry.ty, entry.sys
    | `Tw (_, entry), `TwinR ->
      entry.ty, entry.sys
    | _ ->
      failwith "GlobalEnv.M.lookup: twin mismatch"
end

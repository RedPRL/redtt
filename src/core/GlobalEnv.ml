type 'a param =
  [ `P of 'a
  | `Tw of 'a * 'a
  | `Tick
  | `I
  ]

type ty = Tm.tm
type entry = {ty : ty; sys : (Tm.tm, Tm.tm) Tm.system}
type lock_info = {locks : int; killed : bool; constant : bool}
type t = {env : (Name.t * entry param * lock_info) list; rel : Restriction.t}


let emp () =
  {env = [];
   rel = Restriction.emp ()}

let ext (sg : t) nm param : t =
  {sg with env = (nm, param, {locks = 0; killed = false; constant = false}) :: sg.env}

let ext_tick (sg : t) nm : t =
  {sg with env = (nm, `Tick, {locks = 0; killed = false; constant = false}) :: sg.env}

let ext_dim (sg : t) nm : t =
  {sg with env = (nm, `I, {locks = 0; killed = false; constant = false}) :: sg.env}

let ext_lock (sg : t) : t =
  let go (nm, entry, linfo) =
    nm, entry, {linfo with locks = linfo.locks + 1}
  in
  {sg with env = List.map go sg.env}

let clear_locks (sg : t) : t =
  let go (nm, entry, linfo) =
    nm, entry, {linfo with locks = 0}
  in
  {sg with env = List.map go sg.env}


let rec index_of pred xs =
  match xs with
  | [] -> failwith "index_of"
  | x :: xs ->
    if pred x then 0 else 1 + index_of pred xs

let kill_from_tick (sg : t) nm : t =
  try
    let pred (nm', _, _) = nm = nm' in
    let ix = index_of pred sg.env in
    let go ix' (nm, entry, linfo) =
      if ix' <= ix then
        nm, entry, {linfo with killed = true}
      else
        nm, entry, linfo
    in
    let env = List.mapi go sg.env in
    {sg with env}
  with
  | _ -> sg

let define (sg : t) nm ~ty ~tm =
  let face = Tm.make Tm.Dim0, Tm.make Tm.Dim0, Some tm in
  let sys = [face] in
  {sg with env = (nm, `P {ty; sys}, {locks = 0; killed = false; constant = true}) :: sg.env}

let lookup_entry env nm tw =
  let rec go =
    function
    | [] -> failwith "GlobalEnv.lookup_entry"
    | (nm', prm, linfo) :: env ->
      if nm' = nm then
        if not linfo.constant && (linfo.locks > 0 || linfo.killed) then
          failwith "GlobalEnv.lookup_entry: not accessible (modal!!)"
        else
          match prm, tw with
          | `P a, _ -> a
          | `Tw (a, _), `TwinL -> a
          | `Tw (_, a), `TwinR -> a
          | _ -> failwith "GlobalEnv.lookup_entry"
      else
        go env
  in go env

let lookup_ty sg nm (tw : Tm.twin) =
  let {ty; _} = lookup_entry sg.env nm tw in
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
  let go fmt (nm, p, _) =
    match p with
    | `Tw _ ->
      Format.fprintf fmt "%a[twin]"
        Name.pp nm
    | (`Tick | `I | `P _) ->
      Format.fprintf fmt "%a"
        Name.pp nm
  in
  Format.pp_print_list ~pp_sep go fmt @@ List.rev sg.env

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

  let lookup nm tw =
    let entry =
      try
        lookup_entry Sig.globals.env nm tw
      with
      | exn ->
        Format.eprintf "Internal error: %a[%a] not found in {@[<1>%a@]}@."
          Name.pp nm
          pp_twin tw
          pp Sig.globals;
        raise exn
    in
    entry.ty, entry.sys
end

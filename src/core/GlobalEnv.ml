type 'a param =
  [ `P of 'a
  | `Tw of 'a * 'a
  | `Tick
  ]

type ty = Tm.tm
type entry = {ty : ty; sys : (Tm.tm, Tm.tm) Tm.system}
type lock_info = {locks : int; killed : bool}
type t = {env : (Name.t * entry param * lock_info) list; rel : Restriction.t}


let emp () =
  {env = [];
   rel = Restriction.emp ()}

let ext (sg : t) nm param : t =
  {sg with env = (nm, param, {locks = 0; killed = false}) :: sg.env}

let define (sg : t) nm ~ty ~tm =
  let face = Tm.make Tm.Dim0, Tm.make Tm.Dim0, Some tm in
  let sys = [face] in
  {sg with env = (nm, `P {ty; sys}, {locks = 0; killed = false}) :: sg.env}

let lookup_entry env nm tw =
  let rec go =
    function
    | [] -> failwith "GlobalEnv.lookup_entry"
    | (nm', prm, linfo) :: env ->
      if nm' = nm then
        if linfo.locks > 0 || linfo.killed then
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
    | `P _ ->
      Format.fprintf fmt "%a"
        Name.pp nm
    | `Tw _ ->
      Format.fprintf fmt "%a[twin]"
        Name.pp nm
    | `Tick ->
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

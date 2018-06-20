module T = Map.Make (Name)

type 'a param =
  [ `P of 'a
  | `Tw of 'a * 'a
  ]


type ty = Tm.tm
type entry = {ty : ty; sys : (Tm.tm, Tm.tm) Tm.system}
type t = {env : entry param T.t; rel : Restriction.t}


let emp () =
  {env = T.empty;
   rel = Restriction.emp ()}

let ext (sg : t) nm param : t =
  {sg with env = T.add nm param sg.env}

let define (sg : t) nm ~ty ~tm =
  let face = Tm.make Tm.Dim0, Tm.make Tm.Dim0, Some tm in
  let sys = [face] in
  {sg with env = T.add nm (`P {ty; sys}) sg.env}


let lookup_entry sg nm tw =
  match T.find nm sg, tw with
  | `P x, _ -> x
  | `Tw (x, _), `TwinL -> x
  | `Tw (_, x), `TwinR -> x
  | _ -> failwith "GlobalEnv.lookup_entry"

let lookup_ty sg nm tw =
  let {ty; _} = lookup_entry sg.env nm tw in
  ty

let restriction sg =
  sg.rel

let restrict tr0 tr1 sg =
  let ev_dim tr =
    match Tm.unleash tr with
    | Tm.Up (Tm.Ref {name; _}, Emp) -> `Atom name
    | Tm.Dim0 -> `Dim0
    | Tm.Dim1 -> `Dim1
    | _ -> failwith "Restrict: expected dimension"
  in
  let rel' = Restriction.equate (ev_dim tr0) (ev_dim tr1) sg.rel in
  (* Format.eprintf "Restrict: %a ===> %a@." Restriction.pp sg.rel Restriction.pp rel'; *)
  {sg with rel = rel'}

let pp fmt sg =
  let pp_sep fmt () = Format.fprintf fmt "; " in
  let go fmt (nm, p) =
    match p with
    | `P _ ->
      Format.fprintf fmt "%a"
        Name.pp nm
    | `Tw _ ->
      Format.fprintf fmt "%a[twin]"
        Name.pp nm
  in
  Format.pp_print_list ~pp_sep go fmt @@ T.bindings sg.env

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
    try
      let {ty; sys} = lookup_entry Sig.globals.env nm tw
      in ty, sys
    with
    | exn ->
      Format.eprintf "Internal error: %a[%a] not found in {@[<1>%a@]}@."
        Name.pp nm
        pp_twin tw
        pp Sig.globals;
      raise exn
end

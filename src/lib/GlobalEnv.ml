module T = Map.Make (Name)

type 'a param =
  [ `P of 'a
  | `Tw of 'a * 'a
  ]


type ty = Tm.tm
type entry = {ty : ty; sys : (Tm.tm, Tm.tm) Tm.system}
type t = entry param T.t


let emp = T.empty

let ext (sg : t) nm param : t =
  T.add nm param sg

let define (sg : t) nm ~ty ~tm =
  let face = Tm.make Tm.Dim0, Tm.make Tm.Dim0, Some tm in
  let sys = [face] in
  T.add nm (`P {ty; sys}) sg


let lookup_entry sg nm tw =
  match T.find nm sg, tw with
  | `P x, `Only -> x
  | `Tw (x, _), `TwinL -> x
  | `Tw (_, x), `TwinR -> x
  | _ -> failwith "GlobalEnv.lookup_entry"

let lookup_ty sg nm tw =
  let {ty; _} = lookup_entry sg nm tw in
  ty

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
  Format.pp_print_list ~pp_sep go fmt @@ T.bindings sg

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
  let lookup nm tw =
    try
      let {ty; sys} = lookup_entry Sig.globals nm tw
      in ty, sys
    with
    | exn ->
      Format.eprintf "Internal error: %a[%a] not found in {@[<1>%a@]}@."
        Name.pp nm
        pp_twin tw
        pp Sig.globals;
      raise exn
end

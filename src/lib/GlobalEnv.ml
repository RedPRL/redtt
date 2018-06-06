module T = Map.Make (Name)

type ty = Tm.tm
type entry = {ty : ty; sys : (Tm.tm, Tm.tm) Tm.system}
type t = entry T.t

let emp = T.empty

let ext sg nm ~ty ~sys =
  T.add nm {ty; sys} sg

let define sg nm ~ty ~tm =
  let face = Tm.make Tm.Dim0, Tm.make Tm.Dim0, Some tm in
  let sys = [face] in
  T.add nm {ty; sys} sg

let lookup_ty sg nm _tw =
  let {ty; _} = T.find nm sg in
  ty

let pp fmt sg =
  let pp_sep fmt () = Format.fprintf fmt "; " in
  let go fmt (nm, _) =
    Format.fprintf fmt "%a"
      Name.pp nm
  in
  Format.pp_print_list ~pp_sep go fmt @@ T.bindings sg

module M (Sig : sig val globals : t end) : Val.Sig =
struct
  let lookup nm =
    try
      let {ty; sys} = T.find nm Sig.globals in
      ty, sys
    with
    | exn ->
      Format.eprintf "Internal error: %a not found in {@[<1>%a@]}@."
        Name.pp nm
        pp Sig.globals;
      raise exn
end

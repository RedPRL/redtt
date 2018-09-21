open Tm

type rec_spec =
  | Self

type arg_spec =
  [ `Const of tm
  | `Rec of rec_spec
  | `Dim
  ]

type ('a, 'e) telescope =
  | TNil of 'e
  | TCons of 'a * ('a, 'e) telescope Tm.bnd


type constr = (arg_spec, (tm, tm) system) telescope

module Constr =
struct
  type t = constr

  let open_var _ _ = failwith "TODO"
  let close_var _ _ = failwith "TODO"
  let bind _ _ = failwith "TODO"

  let rec specs =
    function
    | TNil _ -> []
    | TCons (spec, Tm.B (nm, constr)) ->
      (nm, spec) :: specs constr

  let rec boundary =
    function
    | TNil sys -> sys
    | TCons (_, Tm.B (_, constr)) ->
      boundary constr

end

type desc =
  {kind : Kind.t;
   lvl : Lvl.t;
   params : (string * tm) list;
   constrs : (string * constr) list;
   status : [`Complete | `Partial]}



let flip f x y = f y x

let rec dim_specs constr =
  match constr with
  | TNil _ -> []
  | TCons (spec, Tm.B (nm, constr)) ->
    match spec with
    | `Dim -> nm :: dim_specs constr
    | _ -> dim_specs constr


exception ConstructorNotFound of string

let lookup_constr lbl desc =
  try
    let _, constr = List.find (fun (lbl', _) -> lbl' = lbl) desc.constrs in
    constr
  with
  | _ ->
    raise @@ ConstructorNotFound lbl

let is_strict_set desc =
  let constr_is_point constr =
    match dim_specs constr with
    | [] -> true
    | _ -> false
  in
  desc.params = [] && List.fold_right (fun (_, constr) r -> constr_is_point constr && r) desc.constrs true

let pp_string = Uuseg_string.pp_utf_8
let pp_string = Uuseg_string.pp_utf_8

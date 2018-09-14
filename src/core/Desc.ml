type 'a rec_spec =
  | Self


type data_label = string
type con_label = string


type 'a face = 'a * 'a * 'a option
type 'a system = 'a face list

type 'a constr =
  {const_specs : (string * 'a) list;
   rec_specs : (string * 'a rec_spec) list;
   dim_specs : string list;
   boundary : 'a system}


(** A datatype description is just a list of named constructors. *)
type 'a desc =
  {kind : Kind.t;
   lvl : Lvl.t;
   constrs : (con_label * 'a constr) list;
   status : [`Complete | `Partial]}

exception ConstructorNotFound of con_label

let lookup_constr lbl desc =
  try
    let _, constr = List.find (fun (lbl', _) -> lbl' = lbl) desc.constrs in
    constr
  with
  | _ ->
    raise @@ ConstructorNotFound lbl

let is_strict_set desc =
  let constr_is_point constr =
    match constr.dim_specs with
    | [] -> true
    | _ -> false
  in
  List.fold_right (fun (_, constr) r -> constr_is_point constr && r) desc.constrs true

let pp_data_label = Uuseg_string.pp_utf_8
let pp_con_label = Uuseg_string.pp_utf_8

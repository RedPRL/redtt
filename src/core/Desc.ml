type 'a arg_ty =
  | Self


type data_label = string
type con_label = string


module Boundary =
struct
  type 'a term =
    | Var of int
    | Intro of
        { clbl : con_label;
          const_args : 'a list;
          rec_args : 'a term list;
          rs : 'a list}
    (* TODO: fhcom, lam, app *)

  type ('a, 'b) face = 'a * 'a * 'b
  type ('a, 'b) sys = ('a, 'b) face list
end

type ('a, 'b) constr =
  {const_specs : (string * 'a) list;
   rec_specs : (string * 'a arg_ty) list;
   dim_specs : string list;
   boundary : ('a, 'b) Boundary.sys}


(** A datatype description is just a list of named constructors. *)
type ('a, 'b) desc =
  {constrs : (con_label * ('a, 'b) constr) list}

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

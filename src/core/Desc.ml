type 'a rec_spec =
  | Self



type 'a face = 'a * 'a * 'a option
type 'a system = 'a face list

type 'a arg_spec =
  [ `Const of 'a
  | `Rec of 'a rec_spec
  | `Dim
  ]


type 'a constr =
  {specs : (string * 'a arg_spec) list;
   boundary : 'a system}


let flip f x y = f y x

let dim_specs constr =
  List.flatten @@ flip List.map constr.specs @@ function
  | (x, `Dim) -> [x]
  | _ -> []


(** A datatype description is just a list of named constructors. *)
type 'a desc =
  {kind : Kind.t;
   lvl : Lvl.t;
   params : (string * 'a) list;
   constrs : (string * 'a constr) list;
   status : [`Complete | `Partial]}

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

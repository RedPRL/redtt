open Tm

type rec_spec =
  | Self

type arg_spec =
  [ `Const of tm
  | `Rec of rec_spec
  | `Dim
  ]


type constr =
  {specs : (string * arg_spec) list;
   boundary : (tm, tm) system}

type desc =
  {kind : Kind.t;
   lvl : Lvl.t;
   params : (string * tm) list;
   constrs : (string * constr) list;
   status : [`Complete | `Partial]}


let flip f x y = f y x

let dim_specs constr =
  List.flatten @@ flip List.map constr.specs @@ function
  | (x, `Dim) -> [x]
  | _ -> []


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

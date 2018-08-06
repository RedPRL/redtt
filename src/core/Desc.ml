type 'a arg_ty =
  | Self

type 'a tele = 'a list

type 'a constr =
  {params : (string * 'a) tele;
   args : (string * 'a arg_ty) list;
   dims : string list}

type data_label = string
type con_label = string

type 'a desc = (con_label * 'a constr) list

exception ConstructorNotFound of con_label

let lookup_constr lbl desc =
  try
    let _, constr = List.find (fun (lbl', _) -> lbl' = lbl) desc in
    constr
  with
  | _ ->
    raise @@ ConstructorNotFound lbl

let is_strict_set desc =
  let constr_is_point constr =
    match constr.dims with
    | [] -> true
    | _ -> false
  in
  List.fold_right (fun (_, constr) r -> constr_is_point constr && r) desc true

let pp_data_label = Uuseg_string.pp_utf_8
let pp_con_label = Uuseg_string.pp_utf_8


let pp_arg_ty fmt =
  function
  | nm, Self ->
    Format.fprintf fmt "(%a : self)"
      Uuseg_string.pp_utf_8 nm

let pp_constr pp fmt constr =
  let pp_param env fmt (nm, ty) =
    Format.fprintf fmt "(%a : %a)"
      Uuseg_string.pp_utf_8 nm
      (pp env) ty
  in

  let rec go env fmt (ps, args, dims) =
    match ps, args, dims with
    | [nm, p], _, _ ->
      let nm, env' = Pretty.Env.bind (Some nm) env in
      Format.fprintf fmt "%a %a"
        (pp_param env) (nm, p)
        (go env') ([], args, dims)
    | (nm, p) :: ps, _, _ ->
      let nm, env' = Pretty.Env.bind (Some nm) env in
      Format.fprintf fmt "%a %a"
        (pp_param env) (nm, p)
        (go env') (ps, args, dims)
    | [], [], [] ->
      ()
    | [], args, dims ->
      let nms, _env' = Pretty.Env.bindn (List.map (fun x -> Some (fst x)) args) env in
      let pp_sep fmt () = Format.fprintf fmt " " in
      begin
        match dims with
        | [] ->
          Format.fprintf fmt "%a <%a>"
            (Format.pp_print_list ~pp_sep pp_arg_ty) (List.map2 (fun nm (_, aty) -> nm, aty) nms args)
            (Format.pp_print_list ~pp_sep Uuseg_string.pp_utf_8) dims
        | _ ->
          Format.fprintf fmt "<%a>" (Format.pp_print_list ~pp_sep Uuseg_string.pp_utf_8) dims
      end
  in
  go Pretty.Env.emp fmt (constr.params, constr.args, constr.dims)

let pp_labeled_constr pp fmt (lbl, constr) =
  Format.fprintf fmt "| %a @[<hv1>%a@]"
    Uuseg_string.pp_utf_8 lbl
    (pp_constr pp) constr

let pp_constrs pp fmt =
  let pp_sep fmt () = Format.pp_print_newline fmt () in
  Format.pp_print_list ~pp_sep (pp_labeled_constr pp) fmt

let pp_desc pp fmt constrs =
  Format.fprintf fmt "@[<v>data where@ %a@ end@]"
    (pp_constrs pp) constrs

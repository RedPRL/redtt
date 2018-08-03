type 'a arg_ty =
  | Self

type 'a tele = 'a list

type 'a constr =
  {params : (string * 'a) tele;
   args : 'a arg_ty list}

type data_label = string
type con_label = string

type 'a desc = (con_label * 'a constr) list


let is_strict_set _ = true

let pp_data_label = Uuseg_string.pp_utf_8
let pp_con_label = Uuseg_string.pp_utf_8


let pp_arg_ty fmt =
  function
  | Self ->
    Format.fprintf fmt "self"

let pp_constr pp fmt constr =
  let pp_param env fmt (nm, ty) =
    Format.fprintf fmt "(%a : %a)"
      Uuseg_string.pp_utf_8 nm
      (pp env) ty
  in

  let rec go_params env fmt =
    function
    | [nm, p] ->
      let nm, env' = Pretty.Env.bind (Some nm) env in
      Format.fprintf fmt "%a %a"
        (pp_param env) (nm, p)
        (go_args env') constr.args
    | (nm, p) :: ps ->
      let nm, env' = Pretty.Env.bind (Some nm) env in
      Format.fprintf fmt "%a %a"
        (pp_param env) (nm, p)
        (go_params env') ps
    | [] ->
      go_args env fmt constr.args

  and go_args _ fmt =
    function
    | [] ->
      ()
    | args ->
      let pp_sep fmt () = Format.fprintf fmt " " in
      Format.fprintf fmt "of ";
      Format.pp_print_list ~pp_sep pp_arg_ty fmt args

  in
  go_params Pretty.Env.emp fmt constr.params

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


(* let nats : 'a desc =
   ["ze", {params = []; args = []};
   "su", {params = []; args = [Self]}] *)

open RedBasis

exception Not_found = Not_found
exception Invalid_argument = Invalid_argument

let redlib_name = "redlib"
let red_extention = ".red"
let rot_extention = ".red"

type selector = string list

let pp_selector =
  let pp_sep fmt () = Format.eprintf "." in
  Format.pp_print_list ~pp_sep Format.pp_print_string

let find_redlib_root (base_dir : string) : string option =
  SysUtil.protect_cwd @@ fun cur ->
  let rec go cur =
    if Sys.file_exists redlib_name then
      Some cur
    else
      let () = Sys.chdir Filename.parent_dir_name in
      let up = Sys.getcwd () in
      if up = cur then
        None
      else
        go up
  in
  Sys.chdir base_dir;
  go (Sys.getcwd ())

let selector_to_stem ~base_dir selector =
  let module_path = String.concat Filename.dir_sep selector in
  let base_dir = Option.default base_dir (find_redlib_root base_dir) in
  Filename.concat base_dir module_path

let stem_to_red stem = stem ^ red_extention

let stem_to_rot stem = stem ^ rot_extention

let selector_to_red ~base_dir selector =
  stem_to_red @@ selector_to_stem ~base_dir selector

let selector_to_rot ~base_dir selector =
  stem_to_rot @@ selector_to_stem ~base_dir selector

let red_to_stem red =
  match String.sub red (String.length red - 4) 4 with
  | str when str = red_extention -> String.sub red 0 @@ String.length red - 4
  | _ -> raise @@ Invalid_argument "red_to_stem"
  | exception Invalid_argument _ -> raise @@ Invalid_argument "red_to_stem"

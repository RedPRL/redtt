open RedBasis

exception Not_found = Not_found

let redlib_name = "redlib"

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
      let next = Sys.getcwd () in
      if next = cur then
        None
      else
        go next
  in
  Sys.chdir base_dir;
  go (Sys.getcwd ())

let module_to_rel_path ?(extension=None) selector =
  let without_ext = String.concat Filename.dir_sep selector in
  match extension with
  | None -> without_ext
  | Some ext -> String.concat "." [without_ext; ext]

let module_to_path ~base_dir ?(extension=None) selector =
  let module_path = module_to_rel_path ~extension selector in
  let base_dir = Option.default base_dir (find_redlib_root base_dir) in
  let import_path = Filename.concat base_dir module_path in
  if Sys.file_exists import_path then
    import_path
  else begin
    Format.eprintf "@[Could not find the module@ %a@ at@ %s.@]@."
    pp_selector selector import_path;
    raise Not_found
  end

exception CanRudenessHelpMe
let normalize_selector ~base_dir _ = raise CanRudenessHelpMe

open RedBasis

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

let find_module base_dir ?(extension=None) selector : string =
  let module_path = module_to_rel_path ~extension selector in
  let local_path = Filename.concat base_dir module_path in
  if Sys.file_exists local_path then
    local_path
  else
    match find_redlib_root base_dir with
    | None ->
      Format.eprintf "@[Could not find the module@ %a@ at@ %s.@]@."
      pp_selector selector local_path;
      raise Not_found
    | Some new_base_dir ->
      let abs_path = SysUtil.normalize_concat [new_base_dir] module_path in
      if Sys.file_exists abs_path then
        abs_path
      else begin
        Format.eprintf "@[Could not find the module@ %a@ at@ %s@ or@ %s.@]@."
        pp_selector selector local_path abs_path;
        raise Not_found
      end

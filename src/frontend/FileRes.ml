open RedBasis

exception Not_found = Not_found

let redlib_name = "redlib"

type local_selector = string list
type selector = local_selector list

let pp_local_selector =
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

let module_to_rel_path ?(extension=None) local_selector =
  let without_ext = String.concat Filename.dir_sep local_selector in
  match extension with
  | None -> without_ext
  | Some ext -> String.concat "." [without_ext; ext]

let module_to_path_ ~base_dir ?(extension=None) local_selector =
  let module_path = module_to_rel_path ~extension local_selector in
  let local_import_path = Filename.concat base_dir module_path in
  if Sys.file_exists local_import_path then
    `Local local_import_path
  else
    match find_redlib_root base_dir with
    | Some new_base_dir when new_base_dir <> base_dir ->
      let global_import_path = Filename.concat new_base_dir module_path in
      if Sys.file_exists global_import_path then
        `Global global_import_path
      else begin
        Format.eprintf "@[Could not find the module@ %a@ at@ %s@ or@ %s.@]@."
        pp_local_selector local_selector local_import_path global_import_path;
        raise Not_found
      end
    | _ ->
      Format.eprintf "@[Could not find the module@ %a@ at@ %s.@]@."
      pp_local_selector local_selector local_import_path;
      raise Not_found

let module_to_path ~base_dir ?(extension=None) local_selector : string =
  match module_to_path_ ~base_dir ~extension local_selector with
  | `Local p -> SysUtil.normalize_concat p
  | `Global p -> SysUtil.normalize_concat p

exception CanRudenessHelpMe
let normalize_selector ~base_dir _ = raise CanRudenessHelpMe

open RedBasis
open RedTT_Core

type options =
  {file_name : string;
   line_width : int;
   debug_mode : bool}

let print_position outx lexbuf =
  let open Lexing in
  let pos = lexbuf.lex_curr_p in
  Format.fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let set_options options =
  Format.set_margin options.line_width;
  Name.set_debug_mode options.debug_mode

let load options source =
  try
    set_options options;
    let f = SysUtil.normalize options.file_name in
    let mlconf : ML.mlconf = {red_path = f; indent = ""} in
    match source with
    | `Stdin ->
      ignore @@ Importer.M.load_stdin ~persistent_env_opt:None ~mlconf ~file_name:f
    | `File ->
      ignore @@ Importer.M.load_file ~persistent_env_opt:None ~mlconf f
  with
  | ParseError.E (posl, posr) ->
    let loc = Some (posl, posr) in
    let pp fmt () = Format.fprintf fmt "Parse error" in
    Log.pp_message ~loc ~lvl:`Error pp Format.err_formatter ();
    exit 1


let load_file options =
  load options `File

let load_from_stdin options =
  load options `Stdin

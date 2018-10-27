open RedBasis
open RedTT_Core

type options =
  {file_name : string;
   line_width : int;
   debug_mode : bool;
   shell_mode : bool;
   recheck : bool}

let print_position outx lexbuf =
  let open Lexing in
  let pos = lexbuf.lex_curr_p in
  Format.fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let set_options options =
  Format.set_margin options.line_width;
  Name.set_debug_mode options.debug_mode;
  RotIO.set_unsafe_mode options.shell_mode;
  Importer.set_ignore_rot options.recheck

(* MORTAL there's actually already a copy of [Elab] in [Importer]. *)
module Elab = Elaborator.Make (Importer.M)

let execute_ml ~mlconf cmd =
  ignore @@ Contextual.run ~mlconf @@ Elab.eval_cmd cmd

let load options source =
  try
    set_options options;
    let red = SysUtil.normalize options.file_name in
    let mlconf : ML.mlconf = ML.TopModule {indent = ""} in
    execute_ml ~mlconf @@
    match source with
    | `Stdin -> ML.MlTopLoadStdin {red}
    | `File -> ML.MlTopLoadFile red
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

open RedBasis
open RedTT_Core

type options =
  {file_name : string;
   line_width: int;
   debug_mode: bool}

let print_position outx lexbuf =
  let open Lexing in
  let pos = lexbuf.lex_curr_p in
  Format.fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let read_from_channel ~file_name channel =
  let lexbuf = Lexing.from_channel channel in
  let open Lexing in
  lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname = file_name};
  Grammar.mltoplevel Lex.token lexbuf

let read_file file_name =
  let channel = open_in file_name in
  try
    let cmd = read_from_channel ~file_name channel in
    close_in channel;
    cmd
  with
  | exn ->
    close_in channel;
    raise exn

module rec Importer : Elaborator.Import =
struct
  open ML
  let cache = Hashtbl.create 20
  let import ~per_process ~mlconf ~selector =
    let f = FileRes.find_module mlconf.base_dir ~extension:(Some "red") selector in
    let normalized_f = SysUtil.normalize_concat [] f in
    match Hashtbl.find_opt cache normalized_f with
    | None ->
      Format.eprintf "@[%sChecking %s@]@." mlconf.indent normalized_f;
      let res, per_process =
        let mlconf = {base_dir = Filename.dirname f; indent = " " ^ mlconf.indent} in
        let mlcmd = read_file f in
        Runner.execute ~per_process_opt:(Some per_process) ~mlconf ~mlcmd in
      Hashtbl.add cache normalized_f res;
      Format.eprintf "@[%sChecked %s@]@." mlconf.indent normalized_f;
      `New (res, per_process)
    | Some res ->
      Format.eprintf "@[%sLoaded %s@]@." mlconf.indent normalized_f;
      `Cached res
end
and Runner :
sig
  val execute : per_process_opt : Contextual.per_process option -> mlconf : ML.mlconf ->
    mlcmd : ML.mlcmd ML.info -> ResEnv.t * Contextual.per_process
end =
struct
  open ML
  open Contextual
  let execute ~per_process_opt ~mlconf ~mlcmd =
    try
      run ~per_process_opt ~mlconf begin
        bind (Elab.eval_cmd mlcmd.con) @@ fun _ ->
        bind (report_unsolved ~loc:mlcmd.span) @@ fun _ ->
        bind resolver @@ fun res ->
        bind get_per_process @@ fun per_process ->
        ret (res, per_process)
      end
    with
    | exn ->
      Format.eprintf "@[<v3>Encountered error:@; @[<hov>%a@]@]@." PpExn.pp exn;
      exit (-1)
end
and Elab : Elaborator.S = Elaborator.Make (Importer)

let execute_signature base_dir mlcmd =
  let mlconf : ML.mlconf = {base_dir; indent = ""} in
  ignore @@ Runner.execute ~per_process_opt:None ~mlconf ~mlcmd

let set_options options =
  Format.set_margin options.line_width;
  Name.set_debug_mode options.debug_mode

let load options source =
  try
    set_options options;
    let base_dir = Filename.dirname options.file_name in
    execute_signature base_dir @@
    match source with
    | `Stdin -> read_from_channel ~file_name:options.file_name stdin
    | `File -> read_file options.file_name
  with
  | ParseError.E (posl, posr) ->
    let loc = Some (posl, posr) in
    let pp fmt () = Format.fprintf fmt "Parse error" in
    Log.pp_message ~loc ~lvl:`Error pp Format.err_formatter ()

let load_file options =
  load options `File

let load_from_stdin options =
  load options `Stdin

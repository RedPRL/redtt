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

module rec Loader :
sig
  val load : persistent_env_opt : Contextual.persistent_env option -> mlconf : ML.mlconf -> string ->
    [`New of Contextual.persistent_env * ResEnv.t | `Cached of ResEnv.t]
  val import : persistent_env : Contextual.persistent_env -> mlconf : ML.mlconf -> selector : FileRes.selector ->
    [`New of Contextual.persistent_env * ResEnv.t | `Cached of ResEnv.t]
end =
struct
  open ML
  let cache = Hashtbl.create 20
  let load ~persistent_env_opt ~mlconf f =
    match Hashtbl.find_opt cache f with
    | None ->
      Format.eprintf "@[%sChecking %s.@]@." mlconf.indent f;
      let persistent_env, res =
        let mlcmd = read_file f in
        Runner.execute ~persistent_env_opt ~mlconf ~mlcmd
      in
      Hashtbl.add cache f res;
      Format.eprintf "@[%sChecked %s.@]@." mlconf.indent f;
      `New (persistent_env, res)
    | Some res ->
      Format.eprintf "@[%sLoaded %s.@]@." mlconf.indent f;
      `Cached res
  let import ~persistent_env ~mlconf ~selector =
    let f = FileRes.module_to_path ~base_dir:mlconf.base_dir ~extension:(Some "red") selector in
    let mlconf = {base_dir = Filename.dirname f; indent = " " ^ mlconf.indent} in
    load ~persistent_env_opt:(Some persistent_env) ~mlconf f
end
and Runner :
sig
  val execute
    : persistent_env_opt : Contextual.persistent_env option
    -> mlconf : ML.mlconf
    -> mlcmd : ML.mlcmd ML.info
    -> Contextual.persistent_env * ResEnv.t
end =
struct
  module M = Monad.Notation (Contextual)
  open ML open M open Contextual

  let execute ~persistent_env_opt ~mlconf ~mlcmd =
    try
      run ~persistent_env_opt ~mlconf begin
        Elab.eval_cmd mlcmd.con >>
        report_unsolved ~loc:mlcmd.span >>
        resolver
      end
    with
    | exn ->
      Format.eprintf "@[<v3>Encountered error:@; @[<hov>%a@]@]@." PpExn.pp exn;
      exit 1
end
and Elab : Elaborator.S = Elaborator.Make (Loader)

let set_options options =
  Format.set_margin options.line_width;
  Name.set_debug_mode options.debug_mode

let load options source =
  try
    set_options options;
    let f = SysUtil.normalize options.file_name in
    let mlconf : ML.mlconf = {base_dir = Filename.dirname f; indent = ""} in
    match source with
    | `Stdin ->
      let mlcmd = read_from_channel ~file_name:f stdin in
      ignore @@ Runner.execute ~persistent_env_opt:None ~mlconf ~mlcmd
    | `File ->
      ignore @@ Loader.load ~persistent_env_opt:None ~mlconf f
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

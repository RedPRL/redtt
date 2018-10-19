open RedBasis
open RedTT_Core

let cache : (string, ResEnv.t) Hashtbl.t
  = Hashtbl.create 100

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

module rec M :
sig
  val load_file
    : persistent_env_opt : Contextual.persistent_env option
    -> mlconf : ML.mlconf
    -> string
    -> [`New of Contextual.persistent_env * ResEnv.t | `Cached of ResEnv.t]

  val load_stdin
    : persistent_env_opt : Contextual.persistent_env option
    -> mlconf : ML.mlconf
    -> file_name : string
    -> Contextual.persistent_env * ResEnv.t
    
  val import
    : persistent_env : Contextual.persistent_env
    -> mlconf : ML.mlconf
    -> selector : FileRes.selector
    -> [`New of Contextual.persistent_env * ResEnv.t | `Cached of ResEnv.t]
end =
struct
  open ML
  
  let load_file ~persistent_env_opt ~mlconf red_path =
    let stem = FileRes.red_to_stem red_path in
    match Hashtbl.find_opt cache stem with
    | None ->
      Format.eprintf "@[%sChecking %s.@]@." mlconf.indent red_path;
      let persistent_env, res =
        let mlcmd = read_file red_path in
        Runner.execute ~persistent_env_opt ~mlconf ~mlcmd
      in
      Hashtbl.add cache stem res;
      Format.eprintf "@[%sChecked %s.@]@." mlconf.indent red_path;
      `New (persistent_env, res)
    | Some res ->
      Format.eprintf "@[%sLoaded %s.@]@." mlconf.indent red_path;
      `Cached res

  let load_stdin ~persistent_env_opt ~mlconf ~file_name =
    let mlcmd = read_from_channel ~file_name stdin in
    Runner.execute ~persistent_env_opt ~mlconf ~mlcmd

  let import ~persistent_env ~mlconf ~selector =
    let base_dir = Filename.dirname mlconf.red_path in
    let f = FileRes.selector_to_red ~base_dir selector in
    let mlconf = {red_path = f; indent = " " ^ mlconf.indent} in
    load_file ~persistent_env_opt:(Some persistent_env) ~mlconf f
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
and Elab : Elaborator.S = Elaborator.Make (M)

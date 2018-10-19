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
    -> stem : string
    -> Contextual.persistent_env * ResEnv.t
    
  val import
    : persistent_env : Contextual.persistent_env
    -> mlconf : ML.mlconf
    -> selector : FileRes.selector
    -> [`New of Contextual.persistent_env * ResEnv.t | `Cached of ResEnv.t]
end =
struct
  open ML
  
  let load_file ~persistent_env_opt ~mlconf stem =
    let red = FileRes.stem_to_red stem in
    match Hashtbl.find_opt cache stem with
    | None ->
      Format.eprintf "@[%sChecking %s.@]@." mlconf.indent red;
      let persistent_env, res = Runner.execute ~persistent_env_opt ~mlconf ~mlcmd:(read_file red) in
      Hashtbl.add cache stem res;
      Format.eprintf "@[%sChecked %s.@]@." mlconf.indent red;
      `New (persistent_env, res)
    | Some res ->
      Format.eprintf "@[%sLoaded %s.@]@." mlconf.indent stem;
      `Cached res

  let load_stdin ~persistent_env_opt ~mlconf ~stem =
    let mlcmd = read_from_channel ~file_name:(FileRes.stem_to_red stem) stdin in
    Runner.execute ~persistent_env_opt ~mlconf ~mlcmd

  let import ~persistent_env ~mlconf ~selector =
    let base_dir = Filename.dirname mlconf.stem in
    let stem = FileRes.selector_to_stem ~base_dir selector in
    let mlconf = {stem; indent = " " ^ mlconf.indent} in
    load_file ~persistent_env_opt:(Some persistent_env) ~mlconf stem
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

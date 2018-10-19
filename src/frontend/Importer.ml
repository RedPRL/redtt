open RedBasis
open RedTT_Core
open Contextual

let read_from_channel ~filename channel =
  let lexbuf = Lexing.from_channel channel in
  let open Lexing in
  lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname = filename};
  Grammar.mltoplevel Lex.token lexbuf

let read_file filename =
  let channel = open_in filename in
  try
    let cmd = read_from_channel ~filename channel in
    close_in channel;
    cmd
  with
  | exn ->
    close_in channel;
    raise exn

module rec M :
sig
  val include_file : FileRes.filepath -> unit m
  val include_stdin : filename : FileRes.filepath -> unit m
  val import : selector : FileRes.selector -> ResEnv.t m
end =
struct
  module MN = Monad.Notation (Contextual)
  open ML open MN open Contextual

  let try_run ~mlcmd:{con; span} =
    try
      Elab.eval_cmd con >> report_unsolved span
    with
    | exn ->
      Format.eprintf "@[<v3>Encountered error:@; @[<hov>%a@]@]@." PpExn.pp exn;
      exit 1

  let include_file red =
    mlenv <<@> Env.mlconf >>= fun {indent; _} ->
    Format.eprintf "@[%sStarted %s.@]@." indent red;
    let mlcmd = read_file red in
    ignore_local @@ try_run ~mlcmd >>= fun () ->
    Format.eprintf "@[%sFinished %s.@]@." indent red;
    ret ()

  let include_stdin ~filename =
    mlenv <<@> Env.mlconf >>= fun {indent; _} ->
    let mlcmd = read_from_channel ~filename stdin in
    ignore_local @@ try_run ~mlcmd

  let import ~selector =
    assert_top_level >>
    mlenv <<@> Env.mlconf >>= fun {stem; indent} ->
    let base_dir = Filename.dirname stem in

    let new_stem = FileRes.selector_to_stem ~base_dir selector in
    let new_red = FileRes.stem_to_red new_stem in
    let new_indent = " " ^ indent in
    let new_mlconf = {stem = new_stem; indent = new_indent} in

    get_resolver new_stem >>= function
    | None ->
      Format.eprintf "@[%sChecking %s.@]@." indent new_red;
      isolate_module ~mlconf:new_mlconf begin
        try_run (read_file new_red) >> resolver
      end >>= fun res ->
      save_resolver new_stem res >>= fun () ->
      Format.eprintf "@[%sChecked %s.@]@." indent new_red;
      ret res
    | Some res ->
      Format.eprintf "@[%sLoaded %s.[red|rot].@]@." indent new_stem;
      ret res
end
and Elab : Elaborator.S = Elaborator.Make (M)

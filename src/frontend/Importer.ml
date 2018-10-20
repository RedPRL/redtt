open RedBasis
open RedTT_Core
open Contextual

let read_from_channel ~filepath channel =
  let lexbuf = Lexing.from_channel channel in
  let open Lexing in
  lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname = filepath};
  Grammar.mltoplevel Lex.token lexbuf

let read_file filepath =
  let channel = open_in filepath in
  try
    let cmd = read_from_channel ~filepath channel in
    close_in channel;
    cmd
  with
  | exn ->
    close_in channel;
    raise exn

module rec M :
sig
  val top_load_file : FileRes.filepath -> unit m
  val top_load_stdin : red : FileRes.filepath -> unit m
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

  let top_load_file red =
    mlconf >>=
    function
    | InFile _ -> raise ML.WrongMode
    | TopModule {indent} ->
      let stem = FileRes.red_to_stem red in
      let mlconf = ML.InFile {stem; indent} in
      Format.eprintf "@[%sStarted %s.@]@." indent red;
      isolate_module ~mlconf @@ try_run ~mlcmd:(read_file red) >>
      begin
        Format.eprintf "@[%sFinished %s.@]@." indent red;
        ret ()
      end

  let top_load_stdin ~red =
    mlconf >>=
    function
    | InFile _ -> raise ML.WrongMode
    | TopModule {indent} ->
      let stem = FileRes.red_to_stem red in
      let mlconf = ML.InFile {stem; indent} in
      isolate_module ~mlconf @@ try_run ~mlcmd:(read_from_channel ~filepath:red stdin)

  let import ~selector =
    mlconf >>=
    function
    | TopModule _ -> raise ML.WrongMode
    | InFile {stem; indent} ->
      assert_top_level >>
      let base_dir = Filename.dirname stem in

      let stem = FileRes.selector_to_stem ~base_dir selector in
      let indent = " " ^ indent in
      let mlconf = ML.InFile {stem; indent} in

      let red = FileRes.stem_to_red stem in

      get_resolver stem >>= function
      | None ->
        Format.eprintf "@[%sChecking %s.@]@." indent red;
        isolate_module ~mlconf begin
          try_run (read_file red) >> resolver
        end >>= fun res ->
        save_resolver stem res >>
        begin
          Format.eprintf "@[%sChecked %s.@]@." indent red;
          ret res
        end
      | Some res ->
        Format.eprintf "@[%sLoaded %s.[red|rot].@]@." indent stem;
        ret res
end
and Elab : Elaborator.S = Elaborator.Make (M)

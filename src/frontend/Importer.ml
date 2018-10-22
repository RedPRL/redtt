open RedBasis
open RedTT_Core
open NewContextual

let read_from_channel ~filepath channel =
  let lexbuf = Lexing.from_channel channel in
  let open Lexing in
  lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname = filepath};
  Grammar.mltoplevel Lex.token lexbuf

let read_file filepath =
  let channel = open_in_bin filepath in
  match read_from_channel ~filepath channel with
  | cmd -> close_in channel; cmd
  | exception exn -> close_in channel; raise exn

module rec M :
sig
  val top_load_file : FileRes.filepath -> unit m
  val top_load_stdin : red : FileRes.filepath -> unit m
  val import : selector : FileRes.selector -> ResEnv.t m
end =
struct
  module MN = Monad.Notation (NewContextual)
  open ML open MN open NewContextual

  let run ~mlconf ~mlcmd:{con; span} =
    try
      isolate_module ~mlconf begin
        Elab.eval_cmd con >> abort_unsolved span
      end
    with
    | exn ->
      Format.eprintf "@[<v3>Encountered error:@; @[<hov>%a@]@]@." PpExn.pp exn;
      exit 1

  let run_and_get_rot_resolver ~mlconf ~mlcmd:{con; span} =
    try
      isolate_module ~mlconf begin
        Elab.eval_cmd con >> abort_unsolved span >> RotIO.write
      end
    with
    | exn ->
      Format.eprintf "@[<v3>Encountered error:@; @[<hov>%a@]@]@." PpExn.pp exn;
      exit 1

  let top_load_file red =
    mlconf >>=
    function
    | InFile _ | InStdin _ -> raise ML.WrongMode
    | TopModule {indent} ->
      let stem = FileRes.red_to_stem red in
      let redsum = Digest.file red in
      let mlconf = ML.InFile {stem; redsum; indent} in
      Format.eprintf "@[%sStarted %s.@]@." indent red;
      run ~mlconf ~mlcmd:(read_file red) >>
      begin
        Format.eprintf "@[%sFinished %s.@]@." indent red;
        ret ()
      end

  let top_load_stdin ~red =
    mlconf >>=
    function
    | InFile _ | InStdin _ -> raise ML.WrongMode
    | TopModule {indent} ->
      let stem = FileRes.red_to_stem red in
      let mlconf = ML.InStdin {stem; indent} in
      run ~mlconf ~mlcmd:(read_from_channel ~filepath:red stdin)

  let import ~selector =
    mlconf >>=
    function
    | TopModule _ -> raise ML.WrongMode
    | InFile {stem; indent; _} | InStdin {stem; indent} ->
      assert_top_level >>

      let stem = FileRes.selector_to_stem ~stem selector in
      let red = FileRes.stem_to_red stem in
      let redsum = Digest.file red in
      let indent = " " ^ indent in
      let mlconf = ML.InFile {stem; redsum; indent} in

      cached_resolver stem >>= function
      | None ->
        Format.eprintf "@[%sChecking %s.@]@." indent red;
        run_and_get_rot_resolver ~mlconf ~mlcmd:(read_file red) >>= fun (res, _ as rot) ->
        cache_resolver stem rot >>
        begin
          Format.eprintf "@[%sChecked %s.@]@." indent red;
          ret res
        end
      | Some (res, _) ->
        Format.eprintf "@[%sLoaded %s.[red|rot].@]@." indent stem;
        ret res
end
and Elab : NewElaborator.S = NewElaborator.Make (M)

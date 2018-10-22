open RedBasis
open RedTT_Core
open Contextual

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
  module MN = Monad.Notation (Contextual)
  open ML open MN open Contextual

  let cool_error_printer exn =
    Format.eprintf "@[<v3>Encountered error:@;@[<hov>%a@]@]@." PpExn.pp exn;
    exit 1

  let run ~mlconf ~mlcmd:{con; span} =
    isolate_module ~mlconf begin
      try_ begin
        Elab.eval_cmd con >> abort_unsolved span
      end cool_error_printer
    end

  let run_and_rot ~mlconf ~mlcmd:{con; span} =
    isolate_module ~mlconf begin
      try_ begin
        Elab.eval_cmd con >> abort_unsolved span >> RotIO.write
      end cool_error_printer
    end

  let rec import ~selector =
    mlconf >>=
    function
    | TopModule _ -> raise ML.WrongMode
    | InFile {stem; indent; _} | InMem {stem; indent} ->
      assert_top_level >>
      let stem = FileRes.selector_to_stem ~stem selector in
      cached_resolver stem >>= function
      | Some (res, _) -> ret res
      | None ->
        let rotpath = FileRes.stem_to_rot stem in
        RotIO.try_read ~loader:load ~stem >>= function
        | Some (res, _ as rot) ->
          cache_resolver stem rot >> ret res
        | None ->
          let red = FileRes.stem_to_red stem in
          let redsum = Digest.file red in
          let mlconf = ML.InFile {stem; redsum; indent = " " ^ indent} in
          Format.eprintf "@[%sChecking %s.@]@." indent red;
          run_and_rot ~mlconf ~mlcmd:(read_file red) >>= fun (res, _ as rot) ->
          cache_resolver stem rot >>= fun () ->
          Format.eprintf "@[%sChecked %s.@]@." indent red;
          ret res
  and load ~selector = ignore <@>> import ~selector

  let top_load_file red =
    mlconf >>=
    function
    | InFile _ | InMem _ -> raise ML.WrongMode
    | TopModule {indent} ->
      let stem = FileRes.red_to_stem red in
      let rotpath = FileRes.stem_to_rot stem in
      RotIO.try_read ~loader:load ~stem >>= function
      | Some rot ->
        let rotpath = FileRes.stem_to_rot stem in
        cache_resolver stem rot
      | None ->
        let redsum = Digest.file red in
        let mlconf = ML.InFile {stem; redsum; indent = " " ^ indent} in
        Format.eprintf "@[%sChecking %s.@]@." indent red;
        run_and_rot ~mlconf ~mlcmd:(read_file red) >>= fun rot ->
        cache_resolver stem rot >>= fun () ->
        Format.eprintf "@[%sChecked %s.@]@." indent red;
        ret ()

  let top_load_stdin ~red =
    mlconf >>=
    function
    | InFile _ | InMem _ -> raise ML.WrongMode
    | TopModule {indent} ->
      let stem = FileRes.red_to_stem red in
      let mlconf = ML.InMem {stem; indent} in
      run ~mlconf ~mlcmd:(read_from_channel ~filepath:red stdin)
end
and Elab : Elaborator.S = Elaborator.Make (M)

open RedBasis
open RedTT_Core
open Contextual

let ignore_rot = ref false
let set_ignore_rot b = ignore_rot := b

let read_from_channel ~filepath channel =
  let wiretap_buffer = Buffer.create 0 in
  let wiretapped_input bytes size =
    let n = input channel bytes 0 size in
    Buffer.add_subbytes wiretap_buffer bytes 0 n; n
  in
  let lexbuf = Lexing.from_function wiretapped_input in
  let open Lexing in
  lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname = filepath};
  let tree = Grammar.mltoplevel Lex.token lexbuf in
  tree, Digest.string (Buffer.contents wiretap_buffer)

let read_file filepath =
  let channel = open_in_bin filepath in
  match read_from_channel ~filepath channel with
  | cmd -> close_in channel; cmd
  | exception exn -> close_in channel; raise exn

module rec M :
sig
  val top_load_file : FileRes.filepath -> unit m
  val top_load_stdin : red : FileRes.filepath -> unit m
  val import : selector : FileRes.selector -> rotted_resolver m
end =
struct
  module MN = Monad.Notation (Contextual)
  open ML open MN open Contextual

  let cool_error_printer exn =
    Format.eprintf "@[<v3>Encountered error:@;@[<hov>%a@]@]@." PpExn.pp exn;
    Printexc.print_raw_backtrace stderr (Printexc.get_callstack 20);
    Format.eprintf "@.";
    exit 1

  let run_and_rot ~mlconf ~mlcmd:{con; span} =
    isolate_module ~mlconf begin
      begin
        Elab.eval_cmd con >> abort_unsolved span >> RotIO.write
      end
    end

  let rec import ~selector =
    mlconf >>=
    function
    | TopModule _ -> raise ML.WrongMode
    | InFile {stem; indent; _} | InMem {stem; indent} ->
      assert_top_level >>
      let stem = FileRes.selector_to_stem ~stem selector in
      cached_resolver stem >>= function
      | Some rot -> ret rot
      | None ->
        begin
          if !ignore_rot then ret None else begin
            let rotpath = FileRes.stem_to_rot stem in
            RotIO.try_read ~importer:import ~stem
          end
        end >>= function
        | Some rot ->
          cache_resolver stem rot >> ret rot
        | None ->
          let red = FileRes.stem_to_red stem in
          let mlcmd, redsum = read_file red in
          let mlconf = ML.InFile {stem; redsum; indent = " " ^ indent} in
          Format.eprintf "@[%sChecking %s.@]@." indent red;
          run_and_rot ~mlconf ~mlcmd >>= fun (res, _ as rot) ->
          cache_resolver stem rot >>= fun () ->
          Format.eprintf "@[%sChecked %s.@]@." indent red;
          ret rot

  let top_load_file red =
    mlconf >>=
    function
    | InFile _ | InMem _ -> raise ML.WrongMode
    | TopModule {indent} ->
      let stem = FileRes.red_to_stem red in
      begin
        if !ignore_rot then ret None else begin
          let rotpath = FileRes.stem_to_rot stem in
          RotIO.try_read ~importer:import ~stem
        end
      end >>= function
      | Some rot ->
        let rotpath = FileRes.stem_to_rot stem in
        cache_resolver stem rot
      | None ->
        let mlcmd, redsum = read_file red in
        let mlconf = ML.InFile {stem; redsum; indent = " " ^ indent} in
        Format.eprintf "@[%sChecking %s.@]@." indent red;
        run_and_rot ~mlconf ~mlcmd >>= fun rot ->
        cache_resolver stem rot >>= fun () ->
        Format.eprintf "@[%sChecked %s.@]@." indent red;
        ret ()

  let top_load_stdin ~red =
    mlconf >>=
    function
    | InFile _ | InMem _ -> raise ML.WrongMode
    | TopModule {indent} ->
      let stem = FileRes.red_to_stem red in
      let mlcmd, redsum = read_from_channel ~filepath:red stdin in
      let mlconf = ML.InFile {stem; redsum; indent} in
      run_and_rot ~mlconf ~mlcmd >>= fun rot ->
      cache_resolver stem rot
end
and Elab : Elaborator.S = Elaborator.Make (M)

open RedTT_Core
open Lexing

type options =
  {file_name : Lwt_io.file_name;
   line_width: int;
   debug_mode: bool}

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  Format.fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let read_from_channel file_name channel =
  let open Lwt.Infix in
  let (lexbuf, tokens) = Lex.tokens ~file_name channel in
  let checkpoint = Grammar.Incremental.mltoplevel @@ Lexing.lexeme_start_p lexbuf in
  begin
    Lwt.catch (Parse.loop lexbuf tokens checkpoint) @@ fun exn ->
    Lwt_io.printlf "  raised: %s" @@ Printexc.to_string exn >>= fun _ ->
    Lwt_io.printlf "parser :: cleaning up…" >>= fun _ ->
    Lwt_io.close channel >>= fun _ ->
    Lwt.fail exn
  end

let read_file file_name =
  let open Lwt.Infix in
  Lwt_io.open_file ~mode:Lwt_io.Input file_name >>=
  read_from_channel file_name

let execute_signature dirname mlcmd =
  let module I =
  struct
    let cache = Hashtbl.create 20
    let import f =
      let f = Filename.concat dirname f in
      match Hashtbl.find_opt cache f with
      | None ->
        let mlcmd = Lwt_main.run @@ read_file @@ f ^ ".red" in
        Hashtbl.add cache f mlcmd;
        `Elab mlcmd
      | Some _ ->
        `Cached
  end
  in
  let module Elaborator = Elaborator.Make (I) in
  begin
    try
      ignore @@ ElabMonad.run @@ ElabMonad.report @@ Elaborator.eval_cmd mlcmd;
      Diagnostics.terminated ();
      Lwt.return_unit
    with
    | exn ->
      Format.eprintf "@[<v3>Encountered error:@; @[<hov>%a@]@]@." PpExn.pp exn;
      Diagnostics.terminated ();
      exit 1
  end

let set_options options =
  Format.set_margin options.line_width;
  Name.set_debug_mode options.debug_mode

let load_file options =
  set_options options;
  let open Lwt.Infix in
  let dirname = Filename.dirname options.file_name in
  read_file options.file_name >>= execute_signature dirname

let load_from_stdin options  =
  set_options options;
  let open Lwt.Infix in
  let dirname = Filename.dirname options.file_name in
  read_from_channel options.file_name Lwt_io.stdin
  >>= execute_signature dirname

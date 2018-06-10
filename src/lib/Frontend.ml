open Lexing

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  Format.fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let read_file file_name =
  let open Lwt.Infix in
  Lwt_io.open_file ~mode:Lwt_io.Input file_name >>= fun channel ->
  let (lexbuf, tokens) = Lex.tokens ~file_name channel in
  let checkpoint = Grammar.Incremental.esig @@ Lexing.lexeme_start_p lexbuf in
  begin
    Lwt.catch (Parse.loop lexbuf tokens @@ checkpoint) @@ fun exn ->
    Lwt_io.printlf "  raised: %s" @@ Printexc.to_string exn >>= fun _ ->
    Lwt_io.printlf "parser :: cleaning up…" >>= fun _ ->
    Lwt_io.close channel >>= fun _ ->
    Lwt.return []
  end

let load_file file_name =
  let module I =
  struct
    let import f = Lwt_main.run @@ read_file @@ f ^ ".red"
  end
  in
  let module Refine = Refine.Make (I) in
  let open Lwt.Infix in
  read_file file_name >>= fun esig ->
  let _ = Refine.M.run @@ Refine.elab_sig Refine.T.empty esig in
  Lwt.return_unit

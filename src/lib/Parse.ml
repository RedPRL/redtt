[@@@warning "-22"]

include Grammar

module I = Grammar.MenhirInterpreter

let lwt_pp fmt_str ppf value =
  let buf = Buffer.create 0 in
  let fmt = Format.formatter_of_buffer buf in
  Format.fprintf fmt fmt_str ppf value;
  Format.pp_print_flush fmt ();
  Lwt_io.print @@ Buffer.contents buf

module Kind = struct
  type t =
    | ERROR
  let pp fmt = function
    | ERROR ->
      Format.fprintf fmt "ERROR"
end

module Message = struct
  type t = {
    file_name : string;
    line : int;
    column : int;
    kind : Kind.t;
    details : Format.formatter -> unit -> unit
  }

  let pp fmt msg =
    Format.fprintf fmt "@[<h>%a:%a:%a:%a@]@;%a"
      Format.pp_print_string msg.file_name
      Format.pp_print_int msg.line
      Format.pp_print_int msg.column
      Kind.pp msg.kind
      msg.details ()

  let render msg =
    lwt_pp "@[<v 2>%a@]" pp msg

  let make lexbuf ~kind ~details =
    let open Lexing in
    let pos = lexeme_start_p lexbuf in
    let file_name = pos.pos_fname in
    let line = pos.pos_lnum in
    let column = pos.pos_cnum - pos.pos_bol in
    { file_name; line; column; kind; details }
end

module Element = struct
  let handle lexbuf (I.Element (_state, _value, _start_pos, _end_pos)) : Message.t =
    let kind = Kind.ERROR in
    (* let details = begin match I.incoming_symbol state with
      | I.N nonterminal -> Nonterminal.details nonterminal ~value
      | I.T terminal -> Terminal.details terminal ~value
    end in *)
    let details _fmt () = () in
    Message.make lexbuf ~kind ~details
end

let loop lexbuf tokens =
  let rec go checkpoint () =
    begin match checkpoint with
      | I.AboutToReduce (_env, _production) ->
        go (I.resume checkpoint) ()

      | I.Accepted result ->
        let doc = result ResEnv.init in
        Lwt.return @@ Decl.check_document LCx.emp doc

      | I.HandlingError env ->
        begin match I.top env with
          | None ->
            Lwt.return_unit
          | Some element ->
            Message.render @@ Element.handle lexbuf element
        end

      | I.InputNeeded _env ->
        let open Lwt.Infix in
        Lwt_stream.get tokens >>= fun token ->
        begin match token with
          | None ->
            Lwt.fail_with "[parser] token stream ended prematurely"
          | Some lexeme ->
            let start_p = Lexing.lexeme_start_p lexbuf in
            let end_p = Lexing.lexeme_end_p lexbuf in
            go (I.offer checkpoint (lexeme, start_p, end_p)) ()
        end

      | I.Rejected ->
        Lwt.fail_with "parser :: rejected"

      | I.Shifting (_env_before, _env_after, _requests_next_token) ->
        go (I.resume checkpoint) ()
    end in
  go

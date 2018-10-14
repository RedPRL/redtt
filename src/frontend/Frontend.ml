open RedTT_Core

type options =
  {file_name : string;
   line_width: int;
   debug_mode: bool}

let print_position outx lexbuf =
  let open Lexing in
  let pos = lexbuf.lex_curr_p in
  Format.fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

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

let execute_signature dirname mlcmd =
  let open ML in
  let module I =
  struct
    let cache = Hashtbl.create 20
    let import ~path =
      let f = List.fold_left Filename.concat dirname path in
      match Hashtbl.find_opt cache f with
      | None ->
        let mlcmd = read_file @@ f ^ ".red" in
        Hashtbl.add cache f mlcmd.con;
        `Elab mlcmd.con
      | Some _ ->
        `Cached
  end
  in
  let module Elaborator = Elaborator.Make (I) in
  begin
    try
      ignore @@ Contextual.run @@ begin
        Contextual.bind (Elaborator.eval_cmd mlcmd.con) @@ fun _ ->
        Contextual.report_unsolved ~loc:mlcmd.span
      end
    with
    | exn ->
      Format.eprintf "@[<v3>Encountered error:@; @[<hov>%a@]@]@." PpExn.pp exn;
      exit 1
  end

let set_options options =
  Format.set_margin options.line_width;
  Name.set_debug_mode options.debug_mode

let load options source =
  try
    set_options options;
    let dirname = Filename.dirname options.file_name in
    execute_signature dirname @@
    match source with
    | `Stdin -> read_from_channel ~file_name:options.file_name stdin
    | `File -> read_file options.file_name
  with
  | ParseError.E (posl, posr) ->
    let loc = Some (posl, posr) in
    let pp fmt () = Format.fprintf fmt "Parse error" in
    Log.pp_message ~loc ~lvl:`Error pp Format.err_formatter ()

let load_file options =
  load options `File

let load_from_stdin options =
  load options `Stdin

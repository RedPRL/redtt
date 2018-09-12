open Cmdliner
open RedTT

type command = unit Lwt.t Term.t * Term.info

let opt_margin =
  let doc = "Set pretty-printing margin to $(docv) characters." in
  Arg.(value & opt int 80 & info ["line-width"] ~docv:"WIDTH" ~doc)

let opt_file_name =
  Arg.
    ( required
      & pos ~rev:true 0 (some string) None
      & info [] ~doc:"The name of the file being loaded" ~docv:"FILE"
    )

let opts_config =
  let open Term  in
  let make file_name line_width = Frontend.{file_name; line_width} in
  pure make $ opt_file_name $ opt_margin

let cmd_default =
  Term.
    ( ret @@ pure @@ `Help ( `Pager, None )
    , info "redtt" ~version:"0.1.0"
    )

let cmd_help =
  let doc = "show help" in
  Term.
    ( ret @@ pure @@ `Help ( `Pager, None )
    , info "help" ~doc
    )

let cmd_load_file =
  let doc = "load file" in
  Term.
    ( pure Frontend.load_file $ opts_config
    , info "load-file" ~doc
    )

let cmd_from_stdin =
  let doc = "read from stdin" in
  Term.
    ( pure Frontend.load_from_stdin $ opts_config
    , info "from-stdin" ~doc
    )


let cmds : command list = [
  cmd_load_file;
  cmd_from_stdin;
  cmd_help;
]

let main () =
  match Term.eval_choice cmd_default cmds with
  | `Error _e -> exit 1
  | `Ok expr -> Lwt_main.run expr
  | _ -> exit 0

let () =
  if not !Sys.interactive then
    main ()

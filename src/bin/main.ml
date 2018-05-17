open Cmdliner
open RedTT

type command = unit Lwt.t Term.t * Term.info

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
  let file_name = Arg.
                    ( required
                      & pos ~rev:true 0 (some string) None
                      & info [] ~doc ~docv:"FILE"
                    ) in
  Term.
    ( pure Frontend.load_file $ file_name
    , info "load-file" ~doc
    )

let cmds : command list = [
  cmd_load_file;
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

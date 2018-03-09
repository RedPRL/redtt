open Cmdliner

let cmd_help: unit Lwt.t Term.t * Term.info =
  let doc = "show help" in
  Term.
    ( ret @@ pure @@ `Help ( `Pager, None )
    , info "help" ~doc
    )

let cmd_default =
  Term.
    ( ret @@ pure @@ `Help ( `Pager, None )
    , info "cubical" ~version:"0.1.0"
    )

let cmds = [
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

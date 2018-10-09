include module type of Grammar

module I = Grammar.MenhirInterpreter

val loop : Lexing.lexbuf -> I.token Lwt_stream.t -> ML.mlcmd ML.info I.checkpoint -> unit -> ML.mlcmd ML.info Lwt.t

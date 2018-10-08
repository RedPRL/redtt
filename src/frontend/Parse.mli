include module type of Grammar

module I = Grammar.MenhirInterpreter

val loop : Lexing.lexbuf -> I.token Lwt_stream.t -> ML.mlcmd I.checkpoint -> unit -> ML.mlcmd Lwt.t

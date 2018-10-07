open RedTT_Core
include module type of Grammar

module I = Grammar.MenhirInterpreter

val loop : Lexing.lexbuf -> I.token Lwt_stream.t -> ESig.mlcmd I.checkpoint -> unit -> ESig.mlcmd Lwt.t

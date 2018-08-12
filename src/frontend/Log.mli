open RedTT_Core

type level = [`Info | `Error | `Warn]

type location = (Lexing.position * Lexing.position) option

(* TODO: would be nice to figure out how to turn this into our own printf-style function *)
val pp_message
  : loc:location
  -> lvl:level
  -> 'a Pp.t0
  -> Format.formatter
  -> 'a
  -> unit

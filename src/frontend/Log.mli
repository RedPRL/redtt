open RedTT_Core

type level = [`Info | `Error | `Warn]

type location = (Lexing.position * Lexing.position) option

val pp_message
  : loc:location
  -> lvl:level
  -> 'a Pp.t0
  -> Format.formatter
  -> 'a
  -> unit

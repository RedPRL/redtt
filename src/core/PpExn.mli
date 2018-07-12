exception Unrecognized

type printer = Format.formatter -> exn -> unit

val install_printer : printer -> unit

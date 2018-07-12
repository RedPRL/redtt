exception Unrecognized

type printer = Format.formatter -> exn -> unit

let default_printer fmt exn =
  Format.fprintf fmt "Exception: %s" @@ Printexc.to_string exn

let current_printer = ref default_printer

let install_printer printer =
  Printexc.register_printer @@ fun exn ->
  try
    printer Format.str_formatter exn;
    Some (Format.flush_str_formatter ())
  with
  | Unrecognized ->
    None

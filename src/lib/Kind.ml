type t = Kan | Pre

let pp fmt =
  function
  | Kan ->
    Format.fprintf fmt "kan"
  | Pre ->
    Format.fprintf fmt "pre"

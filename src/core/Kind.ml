type t = [`Reg | `Kan | `Pre]

let pp fmt =
  function
  | `Reg ->
    Format.fprintf fmt "reg"
  | `Kan ->
    Format.fprintf fmt "kan"
  | `Pre ->
    Format.fprintf fmt "pre"

let lte k0 k1 =
  match k0, k1 with
  | `Reg, _ -> true
  | _, `Reg -> false
  | `Kan, _ -> true
  | _, `Kan -> false
  | `Pre, `Pre -> true

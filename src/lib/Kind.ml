type t = Kan | Pre

let pp fmt =
  function
  | Kan ->
    Format.fprintf fmt "kan"
  | Pre ->
    Format.fprintf fmt "pre"

let stronger k0 k1 =
  match k0, k1 with
  | Kan, Pre -> true
  | _ -> false

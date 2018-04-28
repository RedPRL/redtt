type t =
  | Dim0
  | Dim1
  | Lvl of int
  | Delete (* used in "forall" *)
  | Named of Symbol.t

type equ = t * t

type compare =
  | Same
  | Apart
  | Indeterminate

val compare : t -> t -> compare

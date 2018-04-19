type t = 
  | Dim0
  | Dim1
  | Lvl of int
  | Gen (* used in "forall" *)

type equ = t * t

type compare =
  | Same
  | Apart
  | Indeterminate

val compare : t -> t -> compare

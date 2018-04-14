type t = 
  | Dim0
  | Dim1
  | Lvl of int

type compare =
  | Same
  | Apart
  | Indeterminate

val compare : t -> t -> compare

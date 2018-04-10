type t = 
  | Dim0
  | Dim1
  | Lvl of Cube.t * int

type compare =
  | Same
  | Apart
  | Indeterminate

val compare : t -> t -> compare

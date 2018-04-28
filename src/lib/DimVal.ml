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

let compare d0 d1 =
  match d0, d1 with
  | Dim0, Dim0 -> Same
  | Dim1, Dim1 -> Same
  | Lvl i, Lvl j ->
    if i = j then Same else Indeterminate
  | Dim0, Dim1 -> Apart
  | Dim1, Dim0 -> Apart
  | Delete, Delete -> Same
  | Named x, Named y -> if x = y then Same else Apart
  | _ -> Indeterminate

type edecl =
  | Define of string * escheme * echk
  | Debug

and escheme = etele * echk
and etele = (string * echk) list

and echk =
  | Hole
  | Lam of string list * echk
  | Pair of echk * echk
  | Type
  | Quo of (ResEnv.t -> Tm.tm)
  | Up of einf

and einf =
  | Var of string

(* e-sigarette ;-) *)
type esig =
  edecl list


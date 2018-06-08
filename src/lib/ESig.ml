type edecl =
  | Define of string * escheme * echk
  | Debug of [ `All | `Constraints ]

and escheme = etele * echk
and etele = (string * echk) list

and echk =
  | Hole of string option
  | Lam of string list * echk
  | Tuple of echk list
  | Type
  | Quo of (ResEnv.t -> Tm.tm)
  | Up of einf

and einf =
  | Var of string

(* e-sigarette ;-) *)
type esig =
  edecl list


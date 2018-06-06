type edecl =
  | Make of string * escheme
  | Refine of string * echk
  | MakeRefine of string * escheme * echk
  | Debug

and escheme = echk

and echk =
  | Hole
  | Lam of string * echk
  | Pair of echk * echk
  | Type
  | Quo of (ResEnv.t -> Tm.tm)
  | Up of einf

and einf =
  | Var of string

(* e-sigarette ;-) *)
type esig =
  edecl list


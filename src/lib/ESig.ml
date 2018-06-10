type edecl =
  | Define of string * escheme * eterm
  | Debug of [ `All | `Constraints | `Unsolved ]

and escheme = etele * eterm
and etele = (string * eterm) list

and eterm =
  | Hole of string option
  | Hope
  | Lam of string list * eterm
  | Tuple of eterm list
  | Type
  | Quo of (ResEnv.t -> Tm.tm)
  | Let of {name : string; ty : eterm; tm : eterm; body : eterm}

  | App of eterm * eterm
  | Var of string

(* e-sigarette ;-) *)
type esig =
  edecl list

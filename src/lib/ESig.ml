type edecl =
  | Define of string * escheme * eterm
  | Debug of [ `All | `Constraints | `Unsolved ]
  | Import of string

and escheme = etele * eterm
and ecell = string * eterm
and etele = ecell list

and eterm =
  | Hole of string option
  | Hope
  | Lam of string list * eterm
  | Tuple of eterm list
  | Type
  | Quo of (ResEnv.t -> Tm.tm)
  | Let of {name : string; ty : eterm option; tm : eterm; body : eterm}

  | Pi of etele * eterm

  | Cut of eterm * frame list

  | Var of string

and frame =
  | App of eterm
  | Car
  | Cdr

(* e-sigarette ;-) *)
type esig =
  edecl list

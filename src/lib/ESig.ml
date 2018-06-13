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

  | If of eterm * eterm * eterm

  | Pi of etele * eterm

  | Cut of eterm * frame list

  | Var of string
  | Num of int

and frame =
  | App of eterm
  | Car
  | Cdr

(* e-sigarette ;-) *)
type esig =
  edecl list


(* Please fill this in. I'm just using it for debugging. *)
let pp fmt =
  function
  | Hole _ ->
    Format.fprintf fmt "<hole>"
  | Hope ->
    Format.fprintf fmt "<hope>"
  | Lam _ ->
    Format.fprintf fmt "<lam>"
  | _ ->
    Format.fprintf fmt "<eterm>"

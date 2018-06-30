open RedTT_Core

type edecl =
  | Define of string * [ `Opaque | `Transparent ] * escheme * eterm
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

  | If of eterm option * eterm * eterm * eterm
  | Bool | Tt | Ff

  | Nat | Zero | Suc of eterm
  | NatRec of eterm * eterm * (string * string * eterm)

  | Int | Pos of eterm | NegSuc of eterm
  | IntRec of eterm * (string * eterm) * (string * eterm)

  | S1Rec of eterm * eterm * (string * eterm)
  | S1 | Base | Loop of eterm

  | Pi of etele * eterm
  | Sg of etele * eterm
  | Ext of string list * eterm * esys
  | Rst of eterm * esys

  | Coe of {r : eterm; r' : eterm; fam : eterm; tm : eterm}
  | HCom of {r : eterm; r' : eterm; cap : eterm; sys : esys}
  | Com of {r : eterm; r' : eterm; fam : eterm; cap : eterm; sys : esys}

  | Cut of eterm * frame list

  | Var of string * int
  | Num of int

and esys = eface list

and eface = eterm * eterm * eterm

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
  | Var (s, _) ->
    Format.fprintf fmt "%s" s
  | _ ->
    Format.fprintf fmt "<eterm>"

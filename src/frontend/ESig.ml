open RedTT_Core
open RedBasis.Bwd

type edecl =
  | Define of string * [ `Opaque | `Transparent ] * escheme * eterm
  | Data of string * eterm Desc.desc
  | Debug of [ `All | `Constraints | `Unsolved ]
  | Import of string
  | Quit

and escheme = etele * eterm
and ecell = [`Ty of string * eterm | `Tick of string | `I of string | `Lock ]
and etele = ecell list

and eterm =
  | Guess of eterm

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
  | NatRec of eterm option * eterm * eterm * (string * string option * eterm)

  | Int | Pos of eterm | NegSuc of eterm
  | IntRec of eterm option * eterm * (string * eterm) * (string * eterm)

  | S1Rec of eterm option * eterm * eterm * (string * eterm)
  | S1 | Base | Loop of eterm

  | Pi of etele * eterm
  | Sg of etele * eterm
  | Ext of string list * eterm * esys
  | Rst of eterm * esys

  | Coe of {r : eterm; r' : eterm; fam : eterm; tm : eterm}
  | HCom of {r : eterm; r' : eterm; cap : eterm; sys : esys}
  | Com of {r : eterm; r' : eterm; fam : eterm; cap : eterm; sys : esys}

  | Shut of eterm

  | TickConst
  | DFixLine of {r : eterm; name : string; ty : eterm; bdy : eterm}
  | FixLine of {r : eterm; name : string; ty : eterm; bdy : eterm}

  | Cut of eterm * frame bwd

  | Var of string * int
  | Num of int

and esys = eface list

and eface = eterm * eterm * eterm

and frame =
  | App of eterm
  | Car
  | Cdr
  | Open

(* e-sigarette ;-) *)
type esig =
  edecl list


(* Please fill this in. I'm just using it for debugging. *)
let rec pp fmt =
  function
  | Hole _ ->
    Format.fprintf fmt "<hole>"
  | Hope ->
    Format.fprintf fmt "<hope>"
  | Lam _ ->
    Format.fprintf fmt "<lam>"
  | Var (s, _) ->
    Format.fprintf fmt "%s" s
  | Zero ->
    Format.fprintf fmt "zero"
  | Suc n ->
    Format.fprintf fmt "(suc %a)" pp n
  | Int ->
    Format.fprintf fmt "int"
  | Pos n ->
    Format.fprintf fmt "(pos %a)" pp n
  | IntRec _ ->
    Format.fprintf fmt "<int-rec>"
  | _ ->
    Format.fprintf fmt "<eterm>"

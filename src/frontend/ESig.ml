open RedTT_Core

type 'a info =
  {con : 'a;
   span : ElabMonad.location}

type edecl =
  | Define of string * [ `Opaque | `Transparent ] * escheme * eterm
  | Data of string * edesc
  | Debug of [ `All | `Constraints | `Unsolved ]
  | Normalize of eterm
  | Import of string
  | Quit


and edesc =
    EDesc of
      {kind : Kind.t;
       lvl : Lvl.t;
       constrs : (string * econstr) list}

and econstr =
    EConstr of
      {specs : ecell list;
       boundary : esys}

and escheme =
  etele * eterm

and ecell =
  [ `Ty of string * eterm
  | `Tick of string
  | `I of string
  ]

and etele = ecell list

and econ =
  | Guess of eterm
  | Hole of string option * eterm option
  | Hope
  | Lam of einvpat list * eterm
  | Tuple of eterm list
  | Type of Kind.t * Lvl.t
  | Quo of (ResEnv.t -> Tm.tm)
  | Let of {pat : einvpat; sch : escheme; tm : eterm; body : eterm}

  | Elim of {mot : eterm option; scrut : eterm; clauses : eclause list}
  | ElimFun of {clauses : eclause list}

  | Pi of etele * eterm
  | Sg of etele * eterm
  | Ext of string list * eterm * esys

  | Coe of {r : eterm; r' : eterm; fam : eterm; tm : eterm}
  | HCom of {r : eterm; r' : eterm; cap : eterm; sys : esys}
  | Com of {r : eterm; r' : eterm; fam : eterm; cap : eterm; sys : esys}

  | Shut of eterm

  | DFixLine of {r : eterm; name : string; ty : eterm; bdy : eterm}
  | FixLine of {r : eterm; name : string; ty : eterm; bdy : eterm}

  | Cut of eterm * frame list

  | Refl

  | Var of {name : string; ushift : int}
  | Num of int

and eterm = econ info

and eclause =
  [ `Con of Desc.con_label * einvpat epatbind list * eterm
  | `All of eterm
  ]

and 'a epatbind =
  [ `Bind of 'a
  | `BindIH of 'a * 'a
  ]

and einvpat =
  [ `Var of [`User of string | `Gen of Name.t]
  | `SplitAs of einvpat * einvpat
  | `Split
  | `Bite of einvpat
  | `Wildcard
  ]

and esys = eface list

and eface = (eterm * eterm) list * eterm

and frame =
  | App of eterm
  | Fst
  | Snd
  | Open


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
  | Var {name; _} ->
    Format.fprintf fmt "%s" name
  | _ ->
    Format.fprintf fmt "<eterm>"

let pp_edecl fmt =
  function
  | Import str ->
    Format.fprintf fmt "import %s" str
  | _ ->
    Format.fprintf fmt "<other>"

let pp_esig =
  Pp.pp_list pp_edecl

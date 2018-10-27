open RedBasis.Bwd

type twin = [`Only | `TwinL | `TwinR]

type 'a bnd = B of string option * 'a
type 'a nbnd = NB of string option bwd * 'a

type ('r, 'a) face = 'r * 'r * 'a option
type ('r, 'a) system = ('r, 'a) face list


type 'a tmf =
  | FHCom of {r : 'a; r' : 'a; cap : 'a; sys : ('a, 'a bnd) system}

  | Univ of {kind : Kind.t; lvl : Lvl.t}
  | Pi of 'a * 'a bnd
  | Ext of ('a * ('a, 'a) system) nbnd
  | Restrict of ('a, 'a) face
  | Sg of 'a * 'a bnd

  | V of {r : 'a; ty0 : 'a; ty1 : 'a; equiv : 'a}
  | VIn of {r : 'a; tm0 : 'a; tm1 : 'a}

  | Lam of 'a bnd
  | ExtLam of 'a nbnd
  | RestrictThunk of ('a, 'a) face

  | Cons of 'a * 'a

  | Dim0
  | Dim1

  | Box of {r : 'a; r' : 'a; cap : 'a; sys : ('a, 'a) system}

  | Up of 'a cmd
  | Let of 'a cmd * 'a bnd

  | Data of {lbl : Name.t; params : 'a list}
  | Intro of Name.t * string * 'a list * 'a list (* TODO: turn this into inline record *)


and 'a head =
  | Meta of {name: Name.t; ushift : int}
  | Var of {name : Name.t; twin : twin; ushift : int}
  | Ix of int * twin
  | Down of {ty : 'a; tm : 'a}
  | DownX of 'a
  | Coe of {r : 'a; r' : 'a; ty : 'a bnd; tm : 'a}
  | HCom of {r : 'a; r' : 'a; ty : 'a; cap : 'a; sys : ('a, 'a bnd) system}
  | Com of {r : 'a; r' : 'a; ty : 'a bnd; cap : 'a; sys : ('a, 'a bnd) system}
  | GHCom of {r : 'a; r' : 'a; ty : 'a; cap : 'a; sys : ('a, 'a bnd) system}
  | GCom of {r : 'a; r' : 'a; ty : 'a bnd; cap : 'a; sys : ('a, 'a bnd) system}


and 'a frame =
  | Fst
  | Snd
  | FunApp of 'a
  | ExtApp of 'a list
  | VProj of {r : 'a; ty0 : 'a; ty1 : 'a; func : 'a}
  | Cap of {r : 'a; r' : 'a; ty : 'a; sys : ('a, 'a bnd) system}
  | RestrictForce

  | Elim of {dlbl : Name.t; params : 'a list; mot : 'a bnd; clauses : (string * 'a nbnd) list}

and 'a spine = 'a frame list
and 'a cmd = 'a head * 'a spine

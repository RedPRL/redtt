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
  | Rst of {ty : 'a; sys : ('a, 'a) system}
  | CoR of ('a, 'a) face
  | Sg of 'a * 'a bnd

  | V of {r : 'a; ty0 : 'a; ty1 : 'a; equiv : 'a}
  | VIn of {r : 'a; tm0 : 'a; tm1 : 'a}

  | Lam of 'a bnd
  | ExtLam of 'a nbnd
  | CoRThunk of ('a, 'a) face

  | Cons of 'a * 'a

  | Dim0
  | Dim1
  | TickConst

  | Box of {r : 'a; r' : 'a; cap : 'a; sys : ('a, 'a) system}

  (* Labelled types from Epigram *)
  | LblTy of {lbl : string; args : ('a * 'a) list; ty : 'a}
  | LblRet of 'a

  | Later of 'a bnd
  | Next of 'a bnd

  | BoxModality of 'a
  | Shut of 'a

  | Up of 'a cmd
  | Let of 'a cmd * 'a bnd

  | Data of Desc.data_label
  | Intro of Desc.data_label * Desc.con_label * 'a list


and 'a head =
  | Meta of {name: Name.t; ushift : int}
  | Var of {name : Name.t; twin : twin; ushift : int}
  | Ix of int * twin
  | Down of {ty : 'a; tm : 'a}
  | DownX of 'a
  | DFix of {r : 'a; ty : 'a; bdy : 'a bnd}
  | Coe of {r : 'a; r' : 'a; ty : 'a bnd; tm : 'a}
  | HCom of {r : 'a; r' : 'a; ty : 'a; cap : 'a; sys : ('a, 'a bnd) system}
  | Com of {r : 'a; r' : 'a; ty : 'a bnd; cap : 'a; sys : ('a, 'a bnd) system}
  | GHCom of {r : 'a; r' : 'a; ty : 'a; cap : 'a; sys : ('a, 'a bnd) system}
  | GCom of {r : 'a; r' : 'a; ty : 'a bnd; cap : 'a; sys : ('a, 'a bnd) system}


and 'a frame =
  | Car
  | Cdr
  | FunApp of 'a
  | ExtApp of 'a list
  | VProj of {r : 'a; ty0 : 'a; ty1 : 'a; equiv : 'a}
  | Cap of {r : 'a; r' : 'a; ty : 'a; sys : ('a, 'a bnd) system}
  | LblCall
  | CoRForce
  | Prev of 'a
  | Open

  | Elim of {dlbl : Desc.data_label; mot : 'a bnd; clauses : (Desc.con_label * 'a nbnd) list}

and 'a spine = 'a frame bwd
and 'a cmd = 'a head * 'a spine

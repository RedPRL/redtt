open RedBasis.Bwd
module DimEnv = Map.Make (Name)

type atom = I.atom
type dir = Dir.t
type dim = I.t

type ('x, 'a) face = ('x, 'a) Face.face


type con =
  | Pi of {dom : value; cod : clo}
  | Sg of {dom : value; cod : clo}
  | Restrict of val_face
  | Ext of ext_abs

  | Coe of {dir : dir; abs : abs; el : value}
  | HCom of {dir : dir; ty : value; cap : value; sys : comp_sys}
  | GHCom of {dir : dir; ty : value; cap : value; sys : comp_sys}
  | FHCom of {dir : dir; cap : value; sys : comp_sys}
  | Box of {dir : dir; cap : value; sys : box_sys}

  | Univ of {kind : Kind.t; lvl : Lvl.t}
  | V of {x : atom; ty0 : value; ty1 : value; equiv : value}
  | VIn of {x : atom; el0 : value; el1 : value}

  | Lam of clo
  | ExtLam of nclo
  | RestrictThunk of val_face

  | Cons of value * value

  | Up of {ty : value; neu : neu; sys : rigid_val_sys}

  | Data of {lbl : Name.t; params : env_el list}

  | Intro of
      {dlbl : Name.t;
       clbl : string;
       args : env_el list;
       sys : rigid_val_sys}

and neu =
  | Lvl of string option * int
  | Var of {name : Name.t; twin : Tm.twin; ushift : int}
  | Meta of {name : Name.t; ushift : int}

  | NHComAtType of {dir : dir; univ : value; ty : neu; ty_sys : rigid_val_sys; cap : value; sys : comp_sys}
  | NHComAtCap of {dir : dir; ty : value; cap : neu; sys : comp_sys}
  | NCoe of {dir : dir; abs : abs; neu : neu}

  | NCoeAtType of {dir : dir; abs : neu_abs; el : value}

  | FunApp of neu * nf
  | ExtApp of neu * dim list
  | Fst of neu
  | Snd of neu

  | Elim of
      {dlbl : Name.t;
       params : env_el list;
       mot : clo;
       neu : neu;
       clauses : (string * nclo) list}

  (* Invariant: neu \in vty, vty is a V type *)
  | VProj of {x : atom; func : nf; neu : neu}
  | Cap of {dir : dir; ty : value; sys : comp_sys; neu : neu}

  | RestrictForce of neu

and nf = {ty : value; el : value}

and abs = value IAbs.abs

and clo =
  | Clo of {bnd : Tm.tm Tm.bnd; rho : env}

and nclo =
  | NClo of {nbnd : Tm.tm Tm.nbnd; rho : env}
  | NCloConst of value Lazy.t

and rigid_abs_face = ([`Rigid], abs) face
and val_face = ([`Any], value) face
and rigid_val_face = ([`Rigid], value) face

and comp_sys = rigid_abs_face list
and val_sys = val_face list
and rigid_val_sys = rigid_val_face list
and box_sys = rigid_val_sys
and ext_abs = (value * val_sys) IAbs.abs
and neu_abs = (neu * val_sys) IAbs.abs

and value = Node of {con : con; action : I.action}

and env_el = [`Val of value | `Dim of I.t]
and env = {cells : env_el bwd; global : dim DimEnv.t}

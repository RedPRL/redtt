open RedBasis.Bwd
module DimEnv = Map.Make (Name)

type atom = I.atom
type dir = Dir.t
type dim = I.t

type ('x, 'a) face = ('x, 'a) Face.face

type tick_gen =
  [`Lvl of string option * int | `Global of Name.t ]

type tick =
  | TickGen of tick_gen


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
  | LblTy of {lbl : string; args : nf list; ty : value}
  | LblRet of value

  | Later of tick_clo
  | Next of tick_clo
  | DFix of {ty : value; clo : clo}
  | DFixLine of {x : atom; ty : value; clo : clo}

  | Data of Desc.data_label
  | Intro of
      {dlbl : Desc.data_label;
       clbl : Desc.con_label;
       const_args : value list;
       rec_args : value list;
       rs : dim list;
       sys : rigid_val_sys}

and neu =
  | Lvl of string option * int
  | Var of {name : Name.t; twin : Tm.twin; ushift : int}
  | Meta of {name : Name.t; ushift : int}

  | NHComAtType of {dir : dir; univ : value; ty : neu; cap : value; sys : comp_sys}
  | NHComAtCap of {dir : dir; ty : value; cap : neu; sys : comp_sys}
  | NCoe of {dir : dir; abs : abs; neu : neu}

  | NCoeAtType of {dir : dir; abs : neu_abs; el : value}

  | FunApp of neu * nf
  | ExtApp of neu * dim list
  | Car of neu
  | Cdr of neu

  | Elim of
      {dlbl : Desc.data_label;
       mot : clo;
       neu : neu;
       clauses : (Desc.con_label * nclo) list}

  (* Invariant: neu \in vty, vty is a V type *)
  | VProj of {x : atom; func : nf; neu : neu}
  | Cap of {dir : dir; ty : value; sys : comp_sys; neu : neu}

  | LblCall of neu
  | RestrictForce of neu

  | Prev of tick * neu
  | Fix of tick_gen * value * clo
  | FixLine of atom * tick_gen * value * clo

and nf = {ty : value; el : value}

and abs = value IAbs.abs

and clo =
  | Clo of {bnd : Tm.tm Tm.bnd; rho : env}

and nclo =
  | NClo of {nbnd : Tm.tm Tm.nbnd; rho : env}
  | NCloConst of value Lazy.t

and bclo =
  | BClo of {len : int; btm : Tm.tm Desc.Boundary.term; rho : env}

and tick_clo =
  | TickClo of {bnd : Tm.tm Tm.bnd; rho : env}
  | TickCloConst of value Lazy.t

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

and env_el = [`Val of value | `Dim of I.t | `Tick of tick]
and env = {cells : env_el bwd; global : dim DimEnv.t}

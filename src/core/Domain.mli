open RedBasis.Bwd

type atom = I.atom
type dir = Dir.t
type dim = I.t

type ('x, 'a) face = ('x, 'a) Face.face

type tick_gen =
  [`Lvl of string option * int | `Global of Name.t ]

type tick =
  | TickConst
  | TickGen of tick_gen


type con =
  | Pi : {dom : value; cod : clo} -> con
  | Sg : {dom : value; cod : clo} -> con
  | Rst : {ty : value; sys : val_sys} -> con
  | CoR : val_face -> con
  | Ext : ext_abs -> con

  | Coe : {dir : dir; abs : abs; el : value} -> con
  | HCom : {dir : dir; ty : value; cap : value; sys : comp_sys} -> con
  | GHCom : {dir : dir; ty : value; cap : value; sys : comp_sys} -> con
  | FCom : {dir : dir; cap : value; sys : comp_sys} -> con
  | Box : {dir : dir; cap : value; sys : box_sys} -> con

  | Univ : {kind : Kind.t; lvl : Lvl.t} -> con
  | V : {x : atom; ty0 : value; ty1 : value; equiv : value} -> con
  | VIn : {x : atom; el0 : value; el1 : value} -> con

  | Lam : clo -> con
  | ExtLam : abs -> con
  | CoRThunk : val_face -> con

  | Cons : value * value -> con
  | Bool : con
  | Tt : con
  | Ff : con

  | Nat : con
  | Zero : con
  | Suc : value -> con

  | Int : con
  | Pos : value -> con
  | NegSuc : value -> con

  | S1 : con
  | Base : con
  | Loop : atom -> con

  | Up : {ty : value; neu : neu; sys : rigid_val_sys} -> con

  | LblTy : {lbl : string; args : nf list; ty : value} -> con
  | LblRet : value -> con

  | Later : tick_clo -> con
  | Next : tick_clo -> con
  | DFix : {ty : value; clo : clo} -> con
  | DFixLine : {x : atom; ty : value; clo : clo} -> con

and neu =
  | Lvl : string option * int -> neu
  | Var : {name : Name.t; twin : Tm.twin; ushift : int} -> neu
  | Meta : {name : Name.t; ushift : int} -> neu
  | FunApp : neu * nf -> neu
  | ExtApp : neu * dim list -> neu
  | Car : neu -> neu
  | Cdr : neu -> neu
  | If : {mot : clo; neu : neu; tcase : value; fcase : value} -> neu

  | NatRec : {mot : clo; neu : neu; zcase : value; scase : nclo} -> neu

  | IntRec : {mot : clo; neu : neu; pcase : clo; ncase : clo} -> neu

  | S1Rec : {mot : clo; neu : neu; bcase : value; lcase : abs} -> neu

  | VProj : {x : atom; ty0 : value; ty1 : value; equiv : value; neu : neu} -> neu

  | Cap : {dir : dir; ty : value; sys : comp_sys; neu : neu} -> neu

  | LblCall : neu -> neu
  | CoRForce : neu -> neu

  | Prev : tick * neu -> neu
  | Fix : tick_gen * value * clo -> neu
  | FixLine : atom * tick_gen * value * clo -> neu

and nf = {ty : value; el : value}

and abs = value IAbs.abs

and clo =
  | Clo of {bnd : Tm.tm Tm.bnd; rho : env}

and nclo =
  | NClo of {nbnd : Tm.tm Tm.nbnd; rho : env}

and tick_clo =
  | TickClo of {bnd : Tm.tm Tm.bnd; rho : env}
  | TickCloConst of value

and rigid_abs_face = ([`Rigid], abs) face
and val_face = ([`Any], value) face
and rigid_val_face = ([`Rigid], value) face

and comp_sys = rigid_abs_face list
and val_sys = val_face list
and rigid_val_sys = rigid_val_face list
and box_sys = rigid_val_sys
and ext_abs = (value * val_sys) IAbs.abs

(* defunctionalized action *)
and dfcon =
  | Con of con
  | Reflect of {ty : value; neu : neu; sys : val_sys}

and value =
  | Node of {con : dfcon; action : I.action}

and env_el = Val of value | Atom of I.t | Tick of tick
and env = {cells : env_el list; global : I.action}


val clo_name : clo -> string option
val nclo_names : nclo -> string option bwd

val pp_abs : Format.formatter -> abs -> unit
val pp_value : Format.formatter -> value -> unit
val pp_dims : Format.formatter -> I.t list -> unit
val pp_neu : Format.formatter -> neu -> unit
val pp_comp_face : Format.formatter -> rigid_abs_face -> unit
val pp_val_face : Format.formatter -> ('x, value) face -> unit
val pp_val_sys : Format.formatter -> ('x, value) face list -> unit
val pp_comp_sys : Format.formatter -> comp_sys -> unit
val pp_names : Format.formatter -> Name.t bwd -> unit


module Env :
sig
  include Sort.S
    with type t = env
    with type 'a m = 'a
  val emp : env
  val clear_locals : env -> env
  val push : env_el -> env -> env
  val push_many : env_el list -> env -> env
end

module Value : Sort.S
  with type t = value
  with type 'a m = 'a


module ExtAbs : IAbs.S
  with type el = value * val_sys

module Abs : IAbs.S
  with type el = value

module ValFace : Face.S with type body := value
module AbsFace : Face.S with type body := abs

module Clo : Sort.S
  with type t = clo
  with type 'a m = 'a

module NClo : Sort.S
  with type t = nclo
  with type 'a m = 'a


module TickClo : Sort.S
  with type t = tick_clo
  with type 'a m = 'a

module CompSys :
sig
  include Sort.S
    with type t = comp_sys
    with type 'a m = [`Ok of comp_sys | `Proj of abs]
  val forall : I.atom -> t -> t
  val forallm : I.atom -> t m -> t m
end

module BoxSys : Sort.S
  with type t = box_sys
  with type 'a m = [`Ok of box_sys | `Proj of value]

module ValSys :
sig
  include Sort.S
    with type t = val_sys
    with type 'a m = 'a

  val from_rigid : rigid_val_sys -> t
  val forall : I.atom -> t -> t
end

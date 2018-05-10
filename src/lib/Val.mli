type atom = Symbol.t
type star = DimStar.t
type gen = DimGeneric.t

type dim = Dim.t

type value
type clo

type ('x, 'a) face = ('x, 'a) Face.face


type con =
  | Pi : {dom : value; cod : clo} -> con
  | Sg : {dom : value; cod : clo} -> con
  | Ext : ext_abs -> con

  | Coe : {dir : star; abs : abs; el : value} -> con
  | HCom : {dir : star; ty : value; cap : value; sys : comp_sys} -> con
  | FCom : {dir : star; cap : value; sys : comp_sys} -> con

  | Univ : Lvl.t -> con
  | V : {x : gen; ty0 : value; ty1 : value; equiv : value} -> con
  | VIn : {x : gen; el0 : value; el1 : value} -> con

  | Lam : clo -> con
  | ExtLam : abs -> con
  | Cons : value * value -> con
  | Bool : con
  | Tt : con
  | Ff : con

  | Up : {ty : value; neu : neu} -> con

and neu =
  | Lvl : int -> neu
  | FunApp : neu * nf -> neu
  | ExtApp : neu * ext_sys * dim -> neu
  | Car : neu -> neu
  | Cdr : neu -> neu
  | If : {mot : clo; neu : neu; tcase : value; fcase : value} -> neu

  (* Invariant: neu \in vty, vty is a V type *)
  | VProj : {x : gen; vty : value; neu : neu; func : value} -> neu

and nf = {ty : value; el : value}

and abs = value Abstraction.abs

and rigid_abs_face = ([`Rigid], abs) face
and val_face = ([`Any], value) face
and rigid_val_face = ([`Rigid], value) face

and comp_sys = rigid_abs_face list
and ext_sys = val_face list
and box_sys = rigid_val_face list
and cap_sys = rigid_abs_face list
and ext_abs = (value * ext_sys) Abstraction.abs

and env_el = Val of value | Atom of atom
and env = env_el list

val into : con -> value
val unleash : value -> con

val eval : env -> 'a Tm.t -> value
val apply : value -> value -> value
val ext_apply : value -> dim -> value
val car : value -> value
val cdr : value -> value

val inst_clo : clo -> value -> value
val const_clo : value -> clo

val unleash_v : value -> gen * value * value * value


module ExtAbs : Abstraction.S
  with type el = value * ext_sys

module Abs : Abstraction.S
  with type el = value

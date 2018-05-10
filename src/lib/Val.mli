type atom = Symbol.t
type star = DimStar.t
type gen = DimGeneric.t

type dim = Dim.t

(* SORTS *)
type can
type neu
type nf

type 'a value
type cfg
type clo

type ('x, 'a) face = ('x, 'a) Face.face
type abs = can value Abstraction.abs

type rigid_abs_face = ([`Rigid], abs) face
type val_face = ([`Any], can value) face
type rigid_val_face = ([`Rigid], can value) face

type comp_sys = rigid_abs_face list
type ext_sys = val_face list
type box_sys = rigid_val_face list
type cap_sys = rigid_abs_face list
type ext_abs = (can value * ext_sys) Abstraction.abs

type _ con =
  | Pi : {dom : can value; cod : clo} -> can con
  | Sg : {dom : can value; cod : clo} -> can con
  | Ext : ext_abs -> can con

  | Coe : {dir : star; abs : abs; el : can value} -> can con
  | HCom : {dir : star; ty : can value; cap : can value; sys : comp_sys} -> can con
  | FCom : {dir : star; cap : can value; sys : comp_sys} -> can con

  | Univ : Lvl.t -> can con
  | V : {x : gen; ty0 : can value; ty1 : can value; equiv : can value} -> can con
  | VIn : {x : gen; el0 : can value; el1 : can value} -> can con

  | Lam : clo -> can con
  | ExtLam : abs -> can con
  | Cons : can value * can value -> can con
  | Bool : can con
  | Tt : can con
  | Ff : can con

  | Up : {ty : can value; neu : neu con} -> can con

  | Lvl : int -> neu con
  | FunApp : neu con * nf con -> neu con
  | ExtApp : neu con * ext_sys * dim -> neu con
  | Car : neu con -> neu con
  | Cdr : neu con -> neu con
  | If : {mot : clo; neu : neu con; tcase : can value; fcase : can value} -> neu con

  (* Invariant: neu \in vty, vty is a V type *)
  | VProj : {x : gen; vty : can value; neu : neu con; func : can value} -> neu con

  | Down : {ty : can value; el : can value} -> nf con


type env_el = Val of can value | Atom of atom
type env = env_el list

val eval : cfg -> can value
val apply : can value -> can value -> can value
val ext_apply : can value -> dim -> can value

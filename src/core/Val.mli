open RedBasis.Bwd

type atom = I.atom
type dir = Dir.t
type dim = I.t

type value
type clo
type tick_clo
type nclo

type ('x, 'a) face = ('x, 'a) Face.face

type tick_gen =
  [`Lvl of string option * int | `Global of Name.t ]

type tick =
  | TickConst
  | TickGen of tick_gen


(* TODO: now it may be possible to semantic domain to use the fancy restriction data structure,
   instead of inventing a new dimension and doing a diagonal. Needs further investigation.

   It was already necessary to *evaluate* with respect to a restriction, based on the needs of the
   typechecker; but the further question is how things should work in the internal semantic operations. *)

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

  (* Invariant: neu \in vty, vty is a V type
  *)
  | VProj : {x : atom; ty0 : value; ty1 : value; equiv : value; neu : neu} -> neu

  | Cap : {dir : dir; ty : value; sys : comp_sys; neu : neu} -> neu

  | LblCall : neu -> neu
  | CoRForce : neu -> neu

  | Prev : tick * neu -> neu
  | Fix : tick_gen * value * clo -> neu
  | FixLine : atom * tick_gen * value * clo -> neu

and nf = {ty : value; el : value}

and abs = value IAbs.abs

and rigid_abs_face = ([`Rigid], abs) face
and val_face = ([`Any], value) face
and rigid_val_face = ([`Rigid], value) face

and comp_sys = rigid_abs_face list
and val_sys = val_face list
and rigid_val_sys = rigid_val_face list
and box_sys = rigid_val_sys
and ext_abs = (value * val_sys) IAbs.abs

and env_el = Val of value | Atom of I.t | Tick of tick

and env

val clo_name : clo -> string option
val nclo_names : nclo -> string option bwd

val pp_abs : Format.formatter -> abs -> unit
val pp_value : Format.formatter -> value -> unit
val pp_dims : Format.formatter -> I.t list -> unit
val pp_neu : Format.formatter -> neu -> unit
val pp_comp_face : Format.formatter -> rigid_abs_face -> unit
val pp_val_sys : Format.formatter -> ('x, value) face list -> unit
val pp_comp_sys : Format.formatter -> comp_sys -> unit
val pp_names : Format.formatter -> Name.t bwd -> unit


module type S =
sig
  val make : con -> value
  val unleash : value -> con

  val make_later : value -> value

  val reflect : value -> neu -> val_sys -> value

  val eval : env -> Tm.tm -> value
  val eval_cmd : env -> Tm.tm Tm.cmd -> value
  val eval_head : env -> Tm.tm Tm.head -> value
  val eval_frame : env -> value -> Tm.tm Tm.frame -> value
  val eval_dim : env -> Tm.tm -> I.t
  val eval_tick : env -> Tm.tm -> tick
  val eval_tm_sys : env -> (Tm.tm, Tm.tm) Tm.system -> val_sys
  val make_closure : env -> Tm.tm Tm.bnd -> clo

  val apply : value -> value -> value
  val ext_apply : value -> dim list -> value
  val prev : tick -> value -> value
  val car : value -> value
  val cdr : value -> value
  val lbl_call : value -> value
  val corestriction_force : value -> value

  val rigid_vproj : atom -> ty0:value -> ty1:value -> equiv:value -> el:value -> value

  val inst_clo : clo -> value -> value
  val inst_nclo : nclo -> value list -> value
  val inst_tick_clo : tick_clo -> tick -> value

  val unleash_pi : value -> value * clo
  val unleash_sg : value -> value * clo
  val unleash_v : value -> atom * value * value * value
  val unleash_later : value -> tick_clo
  val unleash_fcom : value -> dir * value * comp_sys
  val unleash_ext : value -> dim list -> value * val_sys
  val unleash_lbl_ty : value -> string * nf list * value
  val unleash_corestriction_ty : value -> val_face


  module Env :
  sig
    include Sort.S
      with type t = env
      with type 'a m = 'a
    val emp : env
    val clear_locals : env -> env
    val push : env_el -> env -> env
  end

  module Val : Sort.S
    with type t = value
    with type 'a m = 'a


  module ExtAbs : IAbs.S
    with type el = value * val_sys

  module Abs : IAbs.S
    with type el = value

  module Macro : sig
    val equiv : value -> value -> value
  end

  module Error :
  sig
    type t
    val pp : t Pretty.t0
    exception E of t
  end

  val base_restriction : Restriction.t
end

module type Sig =
sig
  val restriction : Restriction.t

  val global_dim : I.atom -> I.t

  (** Return the type and boundary of a global variable *)
  val lookup : Name.t -> Tm.twin -> Tm.tm * (Tm.tm, Tm.tm) Tm.system
end

module M (Sig : Sig) : S

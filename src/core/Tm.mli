open RedBasis.Bwd

type twin = [`Only | `TwinL | `TwinR]

type 'a bnd = B of string option * 'a
type 'a nbnd = NB of string option list * 'a

type info = Lexing.position * Lexing.position

type ('r, 'a) face = 'r * 'r * 'a option
type ('r, 'a) system = ('r, 'a) face list

type 'a tmf =
  | FCom of {r : 'a; r' : 'a; cap : 'a; sys : ('a, 'a bnd) system}

  | Univ of {kind : Kind.t; lvl : Lvl.t}
  | Pi of 'a * 'a bnd
  | Ext of ('a * ('a, 'a) system) nbnd
  | Rst of {ty : 'a; sys : ('a, 'a) system}
  | CoR of ('a, 'a) face
  | Sg of 'a * 'a bnd

  | V of {r : 'a; ty0 : 'a; ty1 : 'a; equiv : 'a}
  | VIn of {r : 'a; tm0 : 'a; tm1 : 'a}

  | Bool
  | Tt
  | Ff

  | Nat
  | Zero
  | Suc of 'a

  | Int
  | Pos of 'a
  | NegSuc of 'a

  | S1
  | Base
  | Loop of 'a

  | Lam of 'a bnd
  | ExtLam of 'a nbnd
  | CoRThunk of ('a, 'a) face

  | Cons of 'a * 'a
  | Dim0
  | Dim1

  | Box of {r : 'a; r' : 'a; cap : 'a; sys : ('a, 'a) system}

  (* Labelled types from Epigram *)
  | LblTy of {lbl : string; args : ('a * 'a) list; ty : 'a}
  | LblRet of 'a

  | Up of 'a cmd
  | Let of 'a cmd * 'a bnd

and 'a head =
  | Meta of {name: Name.t; ushift : int}
  | Ref of {name : Name.t; twin : twin; ushift : int}
  | Ix of int * twin
  | Down of {ty : 'a; tm : 'a}
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
  | If of {mot : 'a bnd; tcase : 'a; fcase : 'a}
  | S1Rec of {mot : 'a bnd; bcase : 'a; lcase : 'a bnd}
  | VProj of {r : 'a; ty0 : 'a; ty1 : 'a; equiv : 'a}
  | Cap of {r : 'a; r' : 'a; ty : 'a; sys : ('a, 'a bnd) system}
  | LblCall
  | CoRForce

and 'a spine = 'a frame bwd
and 'a cmd = 'a head * 'a spine

type tm

val map_head : (tm -> tm) -> tm head -> tm head
val map_frame : (tm -> tm) -> tm frame -> tm frame
val map_spine : (tm -> tm) -> tm spine -> tm spine
val map_tmf : (tm -> tm) -> tm tmf -> tm tmf
val map_tm_sys : (tm -> tm) -> (tm, tm) system -> (tm, tm) system


type 'a subst =
  | Shift of int
  | Dot of 'a * 'a subst


val make : tm tmf -> tm
val unleash : tm -> tm tmf

val close_var : Name.t -> ?twin:(twin -> twin) -> int -> tm -> tm
val open_var : int -> Name.t -> ?twin:(twin -> twin) -> tm -> tm

val bind : Name.t -> tm -> tm bnd
val bindn : Name.t bwd -> tm -> tm nbnd
val unbind : tm bnd -> Name.t * tm
val unbindn : tm nbnd -> Name.t bwd * tm
val unbind_ext : (tm * (tm, tm) system) nbnd -> Name.t bwd * tm * (tm, tm) system
val unbind_ext_with : Name.t list -> (tm * (tm, tm) system) nbnd -> tm * (tm, tm) system
val bind_ext : Name.t bwd -> tm -> (tm, tm) system -> (tm * (tm, tm) system) nbnd

val unbind_with : Name.t -> ?twin:(twin -> twin) -> tm bnd -> tm

val subst : tm cmd subst -> tm -> tm


val shift_univ : int -> tm -> tm

(* make sure you know what you are doing, LOL *)
val eta_contract : tm -> tm


val up : tm cmd -> tm
val ix : ?twin:twin -> int -> tm cmd
val var : ?twin:twin -> Name.t -> tm cmd

val lam : string option -> tm -> tm
val ext_lam : string option list -> tm -> tm
val pi : string option -> tm -> tm -> tm
val sg : string option -> tm -> tm -> tm
val cons : tm -> tm -> tm
val univ : kind:Kind.t -> lvl:Lvl.t -> tm




module Macro :
sig
  val arr : tm -> tm -> tm
  val times : tm -> tm -> tm

  (* non-dependent path *)
  val path : tm -> tm -> tm -> tm

  val is_contr : tm -> tm
  val fiber : ty0:tm -> ty1:tm -> f:tm -> x:tm -> tm
  val equiv : tm -> tm -> tm
end

val pp : tm Pretty.t
val pp0 : tm Pretty.t0
val pp_cmd : tm cmd Pretty.t
val pp_head : tm head Pretty.t
val pp_frame : tm frame Pretty.t
val pp_spine : tm spine Pretty.t
val pp_sys : (tm, tm) system Pretty.t


include Occurs.S with type t := tm

module Sp :
sig
  include Occurs.S with type t = tm spine
end



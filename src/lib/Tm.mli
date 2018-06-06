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
  | Sg of 'a * 'a bnd

  | V of {r : 'a; ty0 : 'a; ty1 : 'a; equiv : 'a}

  | Bool
  | Tt
  | Ff

  | Lam of 'a bnd
  | ExtLam of 'a nbnd

  | Cons of 'a * 'a
  | Dim0
  | Dim1

  (* Labelled types from Epigram *)
  | LblTy of {lbl : string; args : ('a * 'a) list; ty : 'a}
  | LblRet of 'a

  | Up of 'a cmd
  | Let of 'a cmd * 'a bnd

and 'a head =
  | Meta of Name.t
  | Ref of Name.t * twin
  | Ix of int * twin
  | Down of {ty : 'a; tm : 'a}
  | Coe of {r : 'a; r' : 'a; ty : 'a bnd; tm : 'a}
  | HCom of {r : 'a; r' : 'a; ty : 'a; cap : 'a; sys : ('a, 'a bnd) system}
  | Com of {r : 'a; r' : 'a; ty : 'a bnd; cap : 'a; sys : ('a, 'a bnd) system}


and 'a frame =
  | Car
  | Cdr
  | FunApp of 'a
  | ExtApp of 'a list
  | If of {mot : 'a bnd; tcase : 'a; fcase : 'a}
  | VProj of {r : 'a; ty0 : 'a; ty1 : 'a; equiv : 'a}
  | LblCall

and 'a spine = 'a frame bwd
and 'a cmd = 'a head * 'a spine

type tm

val map_head : (tm -> tm) -> tm head -> tm head
val map_frame : (tm -> tm) -> tm frame -> tm frame
val map_spine : (tm -> tm) -> tm spine -> tm spine
val map_tmf : (tm -> tm) -> tm tmf -> tm tmf


type 'a subst =
  | Id
  | Proj
  | Sub of 'a subst * 'a
  | Cmp of 'a subst * 'a subst


val make : tm tmf -> tm
val unleash : tm -> tm tmf

val close_var : Name.t -> twin -> int -> tm -> tm
val open_var : int -> Name.t -> twin -> tm -> tm

val bind : Name.t -> tm -> tm bnd
val bindn : Name.t bwd -> tm -> tm nbnd
val unbind : tm bnd -> Name.t * tm
val unbindn : tm nbnd -> Name.t bwd * tm
val unbind_with : Name.t -> twin -> tm bnd -> tm

val subst : tm cmd subst -> tm -> tm


val up : tm cmd -> tm
val var : int -> twin -> tm cmd
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
val pp_cmd : tm cmd Pretty.t
val pp_head : tm head Pretty.t
val pp_sys : (tm, tm) system Pretty.t


include Occurs.S with type t := tm

module Sp :
sig
  include Occurs.S with type t = tm spine
end

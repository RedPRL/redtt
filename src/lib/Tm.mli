type 'a bnd = B of string option * 'a
type 'a nbnd = NB of string option list * 'a

(* sorts *)
type chk
type head

type 'a t

type 'a face = chk t * chk t * 'a option
type 'a system = 'a face list

type _ f =
  | FCom : {r : chk t; r' : chk t; cap : chk t; sys : chk t bnd system} -> chk f

  | Univ : {kind : Kind.t; lvl : Lvl.t} -> chk f
  | Pi : chk t * chk t bnd -> chk f
  | Ext : (chk t * chk t system) nbnd -> chk f
  | Rst : {ty : chk t; sys : chk t system} -> chk f
  | Sg : chk t * chk t bnd -> chk f

  | V : {r : chk t; ty0 : chk t; ty1 : chk t; equiv : chk t} -> chk f

  | Bool : chk f
  | Tt : chk f
  | Ff : chk f

  | Lam : chk t bnd -> chk f
  | ExtLam : chk t nbnd -> chk f

  | Cons : chk t * chk t -> chk f
  | Dim0 : chk f
  | Dim1 : chk f

  (* Labelled types from Epigram *)
  | LblTy : {lbl : string; args : (chk t * chk t) list; ty : chk t} -> chk f
  | LblRet : chk t -> chk f

  | Ref : Name.t -> head f
  | Ix : int -> head f
  | Down : {ty : chk t; tm : chk t} -> head f
  | Coe : {r : chk t; r' : chk t; ty : chk t bnd; tm : chk t} -> head f
  | HCom : {r : chk t; r' : chk t; ty : chk t; cap : chk t; sys : chk t bnd system} -> head f
  | Com : {r : chk t; r' : chk t; ty : chk t bnd; cap : chk t; sys : chk t bnd system} -> head f

  | Let : cmd * chk t bnd -> chk f
  | Cut : cmd -> chk f

and spine = frame list

and frame =
  | Car
  | Cdr
  | FunApp of chk t
  | ExtApp of chk t list
  | If of {mot : chk t bnd; tcase : chk t; fcase : chk t}
  | VProj of {r : chk t; ty0 : chk t; ty1 : chk t; equiv : chk t}
  | LblCall

and cmd = head t * spine

(** Explicit substitutions in the style of Abadi. *)
type subst =
  | Id
  | Proj
  | Sub of subst * cmd
  | Cmp of subst * subst

val make : 'a f -> 'a t
val unleash : 'a t -> 'a f


val close_var : Name.t -> int -> 'a t -> 'a t
val open_var : int -> Name.t -> 'a t -> 'a t


(** Explicit substitutions are used under the hood, so this is a constant time operation;
    the cost of substituion is spread unleash across calls to [unleash]. *)
val subst : subst -> 'a t -> 'a t

type info = Lexing.position * Lexing.position
val into_info : info option -> 'a f -> 'a t
val info : 'a t -> info option

val var : int -> cmd
val inst0 : cmd -> subst
val up : cmd -> chk t
val lam : string option -> chk t -> chk t
val ext_lam : string option list -> chk t -> chk t
val pi : string option -> chk t -> chk t -> chk t
val sg : string option -> chk t -> chk t -> chk t
val let_ : string option -> cmd -> chk t -> chk t
val cons : chk t -> chk t -> chk t
val univ : kind:Kind.t -> lvl:Lvl.t -> chk t
val car : cmd -> cmd
val cdr : cmd -> cmd

module Macro :
sig
  val arr : chk t -> chk t -> chk t
  val times : chk t -> chk t -> chk t

  (* non-dependent path *)
  val path : chk t -> chk t -> chk t -> chk t

  val is_contr : chk t -> chk t
  val fiber : ty0:chk t -> ty1:chk t -> f:cmd -> x:chk t -> chk t
  val equiv : chk t -> chk t -> chk t
end

val pp : 'a t Pretty.t
val pp_sys : chk t system Pretty.t

type 'a bnd = B of string option * 'a
type 'a nbnd = NB of string option list * 'a

(* sorts *)
type chk
type inf

(** The type of terms, indexed by a sort [chk] or [inf]. See [_ f] for the
    external view, which can be accessed using [unleash]. *)
type 'a t

type 'a face = chk t * chk t * 'a option
type 'a system = 'a face list

(* TODO: add FCom *)

(** The external view of syntactic terms, parameterized by a sort [chk] or [inf].
    We use an indexed family because it simplifies implementation by forcing terms to
    be shaped in a certain way. *)
type _ f =
  | Var : int -> inf f
  | Car : inf t -> inf f
  | Cdr : inf t -> inf f
  | FunApp : inf t * chk t -> inf f
  | ExtApp : inf t * chk t list -> inf f
  | Down : {ty : chk t; tm : chk t} -> inf f
  | Coe : {r : chk t; r' : chk t; ty : chk t bnd; tm : chk t} -> inf f
  | HCom : {r : chk t; r' : chk t; ty : chk t; cap : chk t; sys : chk t bnd system} -> inf f
  | Com : {r : chk t; r' : chk t; ty : chk t bnd; cap : chk t; sys : chk t bnd system} -> inf f

  | FCom : {r : chk t; r' : chk t; cap : chk t; sys : chk t bnd system} -> chk f

  | Up : inf t -> chk f

  | Univ : {kind : Kind.t; lvl : Lvl.t} -> chk f
  | Pi : chk t * chk t bnd -> chk f
  | Ext : (chk t * chk t system) nbnd -> chk f
  | Rst : {ty : chk t; sys : chk t system} -> chk f
  | Sg : chk t * chk t bnd -> chk f

  | V : {r : chk t; ty0 : chk t; ty1 : chk t; equiv : chk t} -> chk f

  | Bool : chk f
  | Tt : chk f
  | Ff : chk f
  | If : {mot : chk t bnd; scrut : inf t; tcase : chk t; fcase : chk t} -> inf f
  | VProj : {r : chk t; tm : chk t; ty0 : chk t; ty1 : chk t; equiv : chk t} -> inf f

  | Lam : chk t bnd -> chk f
  | ExtLam : chk t nbnd -> chk f

  | Cons : chk t * chk t -> chk f
  | Dim0 : chk f
  | Dim1 : chk f

  | Let : inf t * chk t bnd -> chk f

(** Explicit substitutions in the style of Abadi. *)
type subst =
  | Id
  | Proj
  | Sub of subst * inf t
  | Cmp of subst * subst

val make : 'a f -> 'a t
val unleash : 'a t -> 'a f

(** Explicit substitutions are used under the hood, so this is a constant time operation;
    the cost of substituion is spread unleash across calls to [unleash]. *)
val subst : subst -> 'a t -> 'a t

type info = Lexing.position * Lexing.position
val into_info : info option -> 'a f -> 'a t
val info : 'a t -> info option

val var : int -> inf t
val inst0 : inf t -> subst
val up : inf t -> chk t
val lam : string option -> chk t -> chk t
val ext_lam : string option list -> chk t -> chk t
val pi : string option -> chk t -> chk t -> chk t
val sg : string option -> chk t -> chk t -> chk t
val let_ : string option -> inf t -> chk t -> chk t
val cons : chk t -> chk t -> chk t
val univ : kind:Kind.t -> lvl:Lvl.t -> chk t
val car : inf t -> inf t
val cdr : inf t -> inf t

module Macro :
sig
  val arr : chk t -> chk t -> chk t
  val times : chk t -> chk t -> chk t

  (* non-dependent path *)
  val path : chk t -> chk t -> chk t -> chk t

  val is_contr : chk t -> chk t
  val fiber : ty0:chk t -> ty1:chk t -> f:inf t -> x:chk t -> chk t
  val equiv : chk t -> chk t -> chk t
end

val pp : 'a t Pretty.t
val pp_sys : chk t system Pretty.t

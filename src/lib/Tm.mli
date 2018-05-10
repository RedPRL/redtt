type 'a bnd = B of string option * 'a

(* sorts *)
type chk
type inf

(** The type of terms, indexed by a sort [chk] or [inf]. See [_ f] for the
    external view, which can be accessed using [out]. *)
type 'a t

type 'a tube = chk t * chk t * 'a option
type 'a system = 'a tube list

(* TODO: add FCom *)

(** The external view of syntactic terms, parameterized by a sort [chk] or [inf].
    We use an indexed family because it simplifies implementation by forcing terms to
    be shaped in a certain way. *)
type _ f =
  | Var : int -> inf f
  | Car : inf t -> inf f
  | Cdr : inf t -> inf f
  | FunApp : inf t * chk t -> inf f
  | ExtApp : inf t * chk t -> inf f
  | Down : {ty : chk t; tm : chk t} -> inf f
  | Coe : {r : chk t; r' : chk t; ty : chk t bnd; tm : chk t} -> inf f
  | HCom : {r : chk t; r' : chk t; ty : chk t; cap : chk t; sys : chk t bnd system} -> inf f
  | FCom : {r : chk t; r' : chk t; cap : chk t; sys : chk t bnd system} -> inf f
  | Com : {r : chk t; r' : chk t; ty : chk t bnd; cap : chk t; sys : chk t bnd system} -> inf f

  | Up : inf t -> chk f

  | Univ : Lvl.t -> chk f
  | Pi : chk t * chk t bnd -> chk f
  | Ext : (chk t * chk t system) bnd -> chk f
  | Sg : chk t * chk t bnd -> chk f

  | Bool : chk f
  | Tt : chk f
  | Ff : chk f
  | If : {mot : chk t bnd; scrut : inf t; tcase : chk t; fcase : chk t} -> inf f
  | VProj : {r : chk t; tm : inf t; func : chk t} -> inf f

  | Lam : chk t bnd -> chk f
  | ExtLam : chk t bnd -> chk f

  | Cons : chk t * chk t -> chk f
  | Dim0 : chk f
  | Dim1 : chk f

  | Let : inf t * chk t bnd -> chk f

  | Meta : Symbol.t * subst -> inf f

(** Explicit substitutions in the style of Abadi. *)
and subst =
  | Id
  | Proj
  | Sub of subst * inf t
  | Cmp of subst * subst


val into : 'a f -> 'a t
val out : 'a t -> 'a f

type info = Lexing.position * Lexing.position
val into_info : info option -> 'a f -> 'a t
val info : 'a t -> info option

val var : int -> inf t
val inst0 : inf t -> subst
val up : inf t -> chk t
val lam : string option -> chk t -> chk t
val ext_lam : string option -> chk t -> chk t
val pi : string option -> chk t -> chk t -> chk t
val sg : string option -> chk t -> chk t -> chk t
val let_ : string option -> inf t -> chk t -> chk t
val cons : chk t -> chk t -> chk t
val univ : Lvl.t -> chk t
val car : inf t -> inf t
val cdr : inf t -> inf t
val meta : Symbol.t -> subst -> inf t

val pp : 'a t Pretty.t

type 'a bnd = B of string option * 'a

(* sorts *)
type chk
type inf

type 'a t

type 'a tube = chk t * chk t * 'a option
type 'a system = 'a tube list

(* TODO: add FCom *)

type _ f =
  | Var : int -> inf f
  | Car : inf t -> inf f
  | Cdr : inf t -> inf f
  | FunApp : inf t * chk t -> inf f
  | ExtApp : inf t * chk t -> inf f
  | Down : {ty : chk t; tm : chk t} -> inf f
  | Coe : {dim0 : chk t; dim1 : chk t; ty : chk t bnd; tm : chk t} -> inf f
  | HCom : {dim0 : chk t; dim1 : chk t; ty : chk t; cap : chk t; sys : chk t bnd system} -> inf f
  | Com : {dim0 : chk t; dim1 : chk t; ty : chk t bnd; cap : chk t; sys : chk t bnd system} -> inf f  

  | Up : inf t -> chk f

  | Univ : Lvl.t -> chk f
  | Pi : chk t * chk t bnd -> chk f
  | Ext : (chk t * chk t system) bnd -> chk f
  | Sg : chk t * chk t bnd -> chk f
  | Interval : chk f

  | Bool : chk f
  | Tt : chk f
  | Ff : chk f
  | If : {mot : chk t bnd; scrut : inf t; tcase : chk t; fcase : chk t} -> inf f

  | Lam : chk t bnd -> chk f
  | Cons : chk t * chk t -> chk f
  | Dim0 : chk f
  | Dim1 : chk f

  | Let : inf t * chk t bnd -> chk f
  | Meta : Symbol.t * subst -> inf f


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

module Pretty :
sig
  module Env :
  sig
    type t
    val emp : t
    val var : int -> t -> string
    val bind : string option -> t -> string * t
    val bind_fresh : t -> string * t
  end

  val pp : Env.t -> Format.formatter -> 'a t -> unit
end

type var = Thin.t

type 'a bnd = B of 'a

(* sorts *)
type chk
type inf

type 'a t

type 'a tube = chk t * chk t * 'a option
type 'a system = 'a tube list

type _ f =
  | Var : var -> inf f
  | Car : inf t -> inf f
  | Cdr : inf t -> inf f
  | App : inf t * chk t -> inf f
  | Down : {ty : chk t; tm : chk t} -> inf f
  | Coe : {tag : Cube.t; dim0 : chk t; dim1 : chk t; ty : chk t bnd; tm : chk t} -> inf f
  | HCom : {tag : Cube.t; dim0 : chk t; dim1 : chk t; ty : chk t; cap : chk t; sys : chk t bnd system} -> inf f
  | Com : {tag : Cube.t; dim0 : chk t; dim1 : chk t; ty : chk t bnd; cap : chk t; sys : chk t bnd system} -> inf f  

  | Up : inf t -> chk f

  | Univ : Lvl.t -> chk f
  | Pi : chk t * chk t bnd -> chk f
  | Sg : chk t * chk t bnd -> chk f
  | Ext : Cube.t * chk t * chk t system -> chk f
  | Interval : Cube.t -> chk f

  | Lam : chk t bnd -> chk f
  | Cons : chk t * chk t -> chk f
  | Dim0 : chk f
  | Dim1 : chk f

val into : 'a f -> 'a t
val out : 'a t -> 'a f

type info = Lexing.position * Lexing.position
val into_info : info -> 'a f -> 'a t
val info : 'a t -> info option

module Pretty :
sig
  module Env :
  sig
    type t
    val emp : t
    val var : int -> t -> string
    val bind : t -> string * t
  end

  val pp : Env.t -> Format.formatter -> 'a t -> unit
end
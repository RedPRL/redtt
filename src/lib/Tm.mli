type ('i, 'a) tube = 'i * 'i * 'a
type ('i, 'a) system = ('i, 'a) tube list

type atm = Thin.t0
type var = Thin.t0

type 'a vbnd = VB of 'a
type 'a abnd = AB of 'a

(* sorts *)
type chk
type inf

type 'a t

type _ f =
  | Atom : atm -> inf f
  | Var : var -> inf f
  | Car : inf t -> inf f
  | Cdr : inf t -> inf f
  | App : inf t * chk t -> inf f
  | Down : {ty : chk t; tm : chk t} -> inf f
  | Coe : chk t * chk t * chk t abnd * chk t -> inf f
  | HCom : chk t * chk t * chk t * chk t * (chk t, chk t vbnd) system -> inf f

  | Up : inf t -> chk f

  | Univ : Lvl.t -> chk f
  | Pi : chk t * chk t vbnd -> chk f
  | Sg : chk t * chk t vbnd -> chk f
  | Ext : chk t * (chk t, chk t) system -> chk f
  | Interval : chk f

  | Lam : chk t vbnd -> chk f
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
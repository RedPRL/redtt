(* sorts *)
type can
type neu

type tclo
type bclo

type 'a tube = DimVal.t * DimVal.t * 'a option
type 'a system = 'a tube list

type 'a t

type _ f =
  | Lvl : int -> neu f

  | Up : can t * neu t -> can f

  | Pi : tclo * bclo -> can f
  | Sg : tclo * bclo -> can f
  | Restrict : Cube.t * can t * tclo system -> can f
  | Univ : Lvl.t -> can f
  | Interval : Cube.t -> can f

  | Dim0 : can f
  | Dim1 : can f

  | Lam : bclo -> can f
  | Cons : tclo * tclo -> can f

  | Coe : {tag : Cube.t; dim0 : can t; dim1 : can t; ty : bclo; tm : can t} -> can f
  | HCom : {tag : Cube.t; dim0 : can t; dim1 : can t; ty : tclo; cap : can t; sys : bclo system} -> can f

  | App : neu t * can t -> neu f
  | Car : neu t -> neu f
  | Cdr : neu t -> neu f

val into : 'a f -> 'a t
val out : 'a t -> 'a f


module Env : 
sig
  type el = can t

  type t
  val emp : t
  val ext : t -> el -> t

  include DimRel.S with type t := t

  val set_rel : DimRel.t -> t -> t
end


type env = Env.t
type rel = DimRel.t

val eval : env -> 'a Tm.t -> can t

val project_dimval : can t -> DimVal.t
val embed_dimval : DimVal.t -> can t

val eval_clo : tclo -> can t
val inst_bclo : bclo -> can t -> can t

val apply : rel -> can t -> can t -> can t
val car : rel -> can t -> can t
val cdr : rel -> can t -> can t

val reflect : rel -> can t -> neu t -> can t
val generic : rel -> can t -> int -> can t

val out_pi : can t -> tclo * bclo
val out_sg : can t -> tclo * bclo
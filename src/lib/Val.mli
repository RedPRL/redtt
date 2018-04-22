(* sorts *)
type can
type neu
type nf

type tclo
type bclo
type sclo

module Tube :
sig
  type equ = DimVal.equ
  type 'a t = 
    | Indeterminate of equ * 'a
    | True of equ * 'a
    | False of equ
    | Delete
end

type 'a tube = 'a Tube.t
type 'a system = 'a tube list

type 'a t

type _ f =
  | Lvl : int -> neu f

  | Up : can t * neu t -> can f

  | Pi : tclo * bclo -> can f
  | Sg : tclo * bclo -> can f
  | Ext : bclo * sclo -> can f

  | Univ : Lvl.t -> can f
  | Interval : can f

  | Dim0 : can f
  | Dim1 : can f
  | DimDelete : can f
  | DimFresh : Symbol.t -> can f

  | Bool : can f
  | Tt : can f
  | Ff : can f
  | If : {mot : bclo; scrut : neu t; tcase : tclo; fcase : tclo} -> neu f

  | Lam : bclo -> can f
  | Cons : tclo * tclo -> can f

  (* generic coercions in negative types: pi, sigma, extension *)
  | Coe : {dim0 : DimVal.t; dim1 : DimVal.t; ty : bclo; tm : can t} -> can f

  (* generic composites in negative types: pi, sigma, extension *)
  | HCom : {dim0 : DimVal.t; dim1 : DimVal.t; ty : can t; cap : can t; sys : bclo system} -> can f

  (* formal composites in positive types: like the universe, etc. *)
  | FCom : {dim0 : DimVal.t; dim1 : DimVal.t; cap : can t; sys : bclo system} -> can f

  | FunApp : neu t * nf t -> neu f
  | ExtApp : neu t * DimVal.t -> neu f

  | Car : neu t -> neu f
  | Cdr : neu t -> neu f

  | Down : can t * can t -> nf f

val into : 'a f -> 'a t
val out : 'a t -> 'a f

val to_string : 'a t -> string

module Env : 
sig
  type el = can t

  type t
  val emp : t
  val ext : t -> el -> t

  include DimRel.S with type t := t
end


type env = Env.t


val eval : env -> 'a Tm.t -> can t

val project_dimval : can t -> DimVal.t
val embed_dimval : DimVal.t -> can t

val eval_clo : tclo -> can t
val inst_bclo : bclo -> can t -> can t
val inst_sclo : sclo -> DimVal.t -> tclo system

val apply : can t -> can t -> can t
val ext_apply : can t -> DimVal.t -> can t
val car : can t -> can t
val cdr : can t -> can t

val out_pi : can t -> tclo * bclo
val out_sg : can t -> tclo * bclo
val out_ext : can t -> bclo * sclo
val out_nf : nf t -> can t * can t

val generic : can t -> int -> can t
val reflect : can t -> neu t -> can t
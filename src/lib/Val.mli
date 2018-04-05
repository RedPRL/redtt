(* sorts *)
type can
type neu

type 'a bnd = B of 'a


type clo
type bclo

type 'a system

type 'a t
type _ f = 
  | Lvl : int -> neu f

  | Up : can t * neu t -> can f

  | Pi : clo * bclo -> can f
  | Sg : clo * bclo -> can f
  | Ext : can t * clo system -> can f
  | Univ : Lvl.t -> can f
  | Interval : can f

  | Dim0 : can f
  | Dim1 : can f

  | Lam : bclo -> can f
  | Cons : clo * clo -> can f

  | Coe : can t * can t * can t DimFam.t * can t -> can f

  | HCom : can t * can t * can t * can t * can t DimFam.t system -> can f

  | App : neu t * can t -> neu f
  | Car : neu t -> neu f
  | Cdr : neu t -> neu f

val into : 'a f -> 'a t
val out : 'a t -> 'a f

type env = can t list

val eval : env -> 'a Tm.t -> can t

val eval_clo : clo -> can t
val inst_bclo : bclo -> can t -> can t

val apply : can t -> can t -> can t
val car : can t -> can t
val cdr : can t -> can t

val reflect : can t -> neu t -> can t
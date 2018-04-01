(* sorts *)
type can
type neu

type 'a bnd = B of 'a


type clo
type bclo

type _ t = 
  | Idx : int -> can t
  | Lvl : int -> neu t

  | Up : can t * neu t -> can t

  | Pi : clo * bclo -> can t
  | Sg : clo * bclo -> can t
  | Univ : Lvl.t -> can t
  | Interval : can t

  | Lam : bclo -> can t
  | Cons : clo * clo -> can t

  | Coe : can t * can t * can t bnd * can t -> can t

  | App : neu t * can t -> neu t
  | Car : neu t -> neu t
  | Cdr : neu t -> neu t

val thin : Thin.t0 -> 'a t -> 'a t

val eval_clo : clo -> can t
val inst_bclo : bclo -> can t -> can t

val apply : can t -> can t -> can t
val car : can t -> can t
val cdr : can t -> can t

val reflect : can t -> neu t -> can t
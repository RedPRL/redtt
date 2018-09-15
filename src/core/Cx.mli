type cx
type t = cx
type value = Domain.value

val init : GlobalEnv.t -> t
val globals : t -> GlobalEnv.t
val env : t -> Domain.env
val ppenv : t -> Pp.env
val qenv : t -> Quote.env

val clear_locals : t -> t

(* Modal *)
val kill_from_tick : t -> Domain.tick_gen -> t

val ext_ty : t -> nm:string option -> value -> t * value
val ext_dim : t -> nm:string option -> t * I.atom
val ext_dims : t -> nms:string option list -> t * I.atom list
val ext_tick : t -> nm:string option -> t * Domain.tick

(** Might raise I.Inconsistent *)
val restrict : t -> I.t -> I.t -> t * I.action

val def : t -> nm:string option -> ty:value -> el:value -> t
val def_dim : t -> nm:string option -> I.t -> t




(** Look up the classifier (either type, interval or tick) of a local variable. *)
val lookup : int -> t -> [`Ty of value | `I | `Tick]

(** Look up the type of a named constant. *)
val lookup_constant : Name.t -> Tm.twin -> t -> Tm.tm

val make_closure : t -> Tm.tm Tm.bnd -> Domain.clo


val eval : t -> Tm.tm -> value
val eval_cmd : t -> Tm.tm Tm.cmd -> value
val eval_head : t -> Tm.tm Tm.head -> value
val eval_frame : t -> value -> Tm.tm Tm.frame -> value
val eval_dim : t -> Tm.tm -> I.t
val eval_tick : t -> Tm.tm -> Domain.tick
val eval_tm_sys : t -> (Tm.tm, Tm.tm) Tm.system -> Domain.val_sys


val check_eq : t -> ty:value -> value -> value -> unit
val check_subtype : t -> value -> value -> unit
val quote : t -> ty:value -> value -> Tm.tm
val quote_ty : t -> value -> Tm.tm
val quote_dim : t -> I.t -> Tm.tm
val check_eq_ty : t -> value -> value -> unit

val evaluator : t -> (module Val.S)
val quoter : t -> (module Quote.S)

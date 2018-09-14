type value = Domain.value
type cx = Cx.t

module Error :
sig
  type t
  exception E of t
  val pp : t Pp.t0
end

val check_ : cx -> value -> Domain.val_sys -> Tm.tm -> unit
val check : cx -> value -> Tm.tm -> unit
val infer : cx -> Tm.tm Tm.cmd -> value

val check_constr_boundary_sys
  : cx
  -> Desc.data_label
  -> (Tm.tm, Tm.tm) Desc.desc
  -> (Tm.tm, Tm.tm) Tm.system
  -> unit

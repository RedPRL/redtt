type value = Domain.value
type cx = Cx.t

module Error :
sig
  type t
  exception E of t
  val pp : t Pretty.t0
end

val check : cx -> value -> Tm.tm -> unit
val infer : cx -> Tm.tm Tm.cmd -> value
val check_boundary : cx -> value -> Domain.val_sys -> Tm.tm -> unit

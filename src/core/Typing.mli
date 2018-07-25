type value = Domain.value
type cx = LocalCx.t

module type S =
sig
  module CxUtil : LocalCx.S
  module Error :
  sig
    type t
    exception E of t
    val pp : t Pretty.t0
  end

  val check : cx -> value -> Tm.tm -> unit
  val infer : cx -> Tm.tm Tm.cmd -> value
  val check_boundary : cx -> value -> Domain.val_sys -> Tm.tm -> unit
end

module M (Sig : sig val globals : GlobalEnv.t end) : S

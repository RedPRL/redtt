type value = Val.value
type cx = LocalCx.t

module type S =
sig
  module Cx : LocalCx.S
  val check : cx -> Val.value -> Tm.tm -> unit
  val infer : cx -> Tm.tm Tm.cmd -> value
  val check_boundary : cx -> Val.value -> Val.val_sys -> Tm.tm -> unit
end

module M (Sig : sig val globals : GlobalCx.t end) : S with type Cx.t := cx

type value = Val.value
type cx = LocalCx.t

module type S =
sig
  module Cx : LocalCx.S
  val check : cx -> value -> Tm.tm -> unit
  val infer : cx -> Tm.tm Tm.cmd -> value
  val infer_frame : cx -> ty:value -> hd:value -> Tm.tm Tm.frame -> value
  val check_boundary : cx -> value -> Val.val_sys -> Tm.tm -> unit
end

module M (Sig : sig val globals : GlobalCx.t end) : S

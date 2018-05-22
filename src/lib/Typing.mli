type value = Val.value
type cx = LocalCx.t

module type S =
sig
  module Cx : LocalCx.S with type t = cx
  val check : cx -> Val.value -> Tm.chk Tm.t -> unit
  val infer : cx -> Tm.inf Tm.t -> value
  val check_boundary : cx -> Val.value -> Val.val_sys -> Tm.chk Tm.t -> unit
end

module M (Sig : sig val globals : GlobalCx.t end) : S

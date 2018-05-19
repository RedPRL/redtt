type value = Val.value

module Cx = LocalCx
type cx = Cx.t

val check : cx -> Val.value -> Tm.chk Tm.t -> unit
val infer : cx -> Tm.inf Tm.t -> value

val check_boundary : cx -> Val.value -> Val.val_sys -> Tm.chk Tm.t -> unit

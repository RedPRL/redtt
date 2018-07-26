type value = Domain.value
type cx = LocalCx.t

module type S =
sig
  module Error :
  sig
    type t
    exception E of t
    val pp : t Pretty.t0
  end

  val check : cx -> value -> Tm.tm -> unit
  val infer : cx -> Tm.tm Tm.cmd -> value
  val check_boundary : cx -> value -> Domain.val_sys -> Tm.tm -> unit

  (* Basic local context, empty except for global constants and restrictions. *)
  val base_cx : cx

  (* Basic evaluator, set up with global constants and restrictions *)
  module Eval : Val.S
end

module M (Sig : sig val globals : GlobalEnv.t end) : S

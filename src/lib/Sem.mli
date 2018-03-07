open Tm
open Val

module Variance :
sig
  type t = Co | Contra | Iso | None

  val flip : t -> t
end


(* Invariant: all these functions should be called on things which are already typechecked. *)

val apply : d -> d -> d

val eval : env -> chk -> d
val eval_inf : env -> inf -> d

val approx_nf : vr:Variance.t -> ctx:Ctx.t -> ty:d -> lhs:d -> rhs:d -> Tm.chk

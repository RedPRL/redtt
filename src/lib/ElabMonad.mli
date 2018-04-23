type mcx = MCx.t
type lcx = LCx.t
type rnv = ResEnv.t
type menv = MEnv.t
type hole = Symbol.t

type 'a m

val (>>=) : 'a m -> ('a -> 'b m) -> 'b m
val (>>) : 'a m -> 'b m -> 'b m
val ret : 'a -> 'a m

(* TODO: 
   Expose a *local* interface, where the focused hole is part of the state.
   This will simplify the use of this monad considerably. *)

val lookup_goal : hole -> (lcx * rnv * Tm.chk Tm.t) m
val lookup_res : hole -> rnv m

val new_goal : lcx:lcx -> rnv:rnv -> ty:Tm.chk Tm.t -> hole m

val fill : hole -> Tm.chk Tm.t -> unit m

val eval : Val.env -> 'a Tm.t -> Val.can Val.t m

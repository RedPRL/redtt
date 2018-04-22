type mcx = MCx.t
type lcx = LCx.t
type rnv = ResEnv.t
type menv = MEnv.t
type hole = Symbol.t

type 'a m

val (>>=) : 'a m -> ('a -> 'b m) -> 'b m
val (>>) : 'a m -> 'b m -> 'b m
val ret : 'a -> 'a m

val get_env : mcx m
val get_menv : menv m

val lookup : hole -> MCx.sequent m
val lookup_goal : hole -> (lcx * rnv * Tm.chk Tm.t) m
val lookup_res : hole -> rnv m

val new_goal : MCx.sequent -> hole m
val fill : hole -> Tm.chk Tm.t -> unit m

val eval : Val.env -> 'a Tm.t -> Val.can Val.t m

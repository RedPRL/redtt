open RedBasis
open Dev

include Monad.S

val ask : params m
val local : (params -> params) -> 'a m -> 'a m

val popl : entry m
val popr : entry m
val optional : 'a m -> 'a option m

val pushl : entry -> unit m
val pushr : entry -> unit m
val pushls : entry list -> unit m
val go_left : unit m

val unleash_subst : Name.t -> tm -> unit m

val in_scope : Name.t -> param -> 'a m -> 'a m
val lookup_var : Name.t -> twin -> ty m
val lookup_meta : Name.t -> ty m

val postpone : status -> problem -> unit m
val active : problem -> unit m
val block : problem -> unit m


val check : ty:ty -> tm -> bool m
val check_eq : ty:ty -> tm -> tm -> bool m

val typechecker : (module Typing.S) m

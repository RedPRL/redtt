open RedTT_Core
open RedBasis
open Dev

include Monad.S

val ask : params m
val local : (params -> params) -> 'a m -> 'a m
val fix : ('a m -> 'a m) -> 'a m

val isolate : 'a m -> 'a m

val popl : entry m
val popr : entry m
val popr_opt : entry option m

val push_update : Name.t -> unit m

val optional : 'a m -> 'a option m

val pushl : entry -> unit m
val pushr : entry -> unit m
val pushls : entry list -> unit m

val go_to_top : unit m
val go_left : unit m

val in_scope : Name.t -> ty param -> 'a m -> 'a m
val in_scopes : (Name.t * ty param) list -> 'a m -> 'a m
val under_restriction : tm -> tm -> 'a m -> 'a option m

val lookup_var : Name.t -> twin -> ty m
val lookup_meta : Name.t -> (ty * [`Rigid | `Flex]) m

val postpone : status -> problem -> unit m
val active : problem -> unit m
val block : problem -> unit m


val check : ty:ty -> tm -> [`Ok | `Exn of exn] m
val check_subtype : ty -> ty -> [`Ok | `Exn of exn] m
val check_eq : ty:ty -> tm -> tm -> [`Ok | `Exn of exn] m
val check_eq_dim : tm -> tm -> bool m


val get_global_env : Subst.t m
val typechecker : (module Typing.S) m

val dump_state : Format.formatter -> string -> [`All | `Constraints | `Unsolved] -> unit m

val run : 'a m -> 'a

open RedTT_Core
open RedBasis
open Dev

include Monad.S

val ask : params m
val local : (params -> params) -> 'a m -> 'a m
val fix : ('a m -> 'a m) -> 'a m

val assert_top_level : unit m

val modify_mlenv : (ML.mlenv -> ML.mlenv) -> unit m
val mlenv : ML.mlenv m
val mlconf : ML.mlconf m

val resolver : ResEnv.t m
val modify_top_resolver : (ResEnv.t -> ResEnv.t) -> unit m
val declare_datatype : src:string -> ResEnv.visibility -> Name.t -> Desc.desc -> unit m
val replace_datatype : Name.t -> Desc.desc -> unit m

val source_stem : Name.t -> FileRes.filepath option m
val get_resolver : FileRes.filepath -> ResEnv.t option m
val save_resolver : FileRes.filepath -> ResEnv.t -> unit m

val isolate_local : 'a m -> 'a m
val isolate_module : mlconf : ML.mlconf -> 'a m -> 'a m
val run : mlconf : ML.mlconf -> 'a m -> 'a

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


val check : ty:ty -> ?sys:(tm, tm) Tm.system -> tm -> [`Ok | `Exn of exn] m
val check_subtype : ty -> ty -> [`Ok | `Exn of exn] m
val check_eq : ty:ty -> tm -> tm -> [`Ok | `Exn of exn] m
val check_eq_dim : tm -> tm -> bool m


val global_env : Subst.t m
val base_cx : Cx.t m

val dump_state : Format.formatter -> string -> [`All | `Constraints | `Unsolved] -> unit m

val all_solved : bool m
val report_unsolved : loc:Log.location -> unit m

open RedBasis
open RedTT_Core
open Dev

include Monad.S

val optional : 'a m -> 'a option m

val lift : 'a Contextual.m -> 'a m
val in_scope : Name.t -> ty param -> 'a m -> 'a m
val in_scopes : (Name.t * ty param) list -> 'a m -> 'a m
val under_restriction : tm -> tm -> 'a m -> 'a option m
val local : (params -> params) -> 'a m -> 'a m

val isolate : 'a m -> 'a m
val unify : unit m

type location = Log.location

type diagnostic =
  | UserHole of
      {name : string option;
       tele : Unify.telescope;
       ty : Tm.tm;
       tm : Tm.tm}
  | PrintTerm of
      {ty : Tm.tm;
       tm : Tm.tm}

val emit : location -> diagnostic -> unit m
val report : 'a m -> 'a m

val run : 'a m -> 'a

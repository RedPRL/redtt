open Dev
open Contextual
open RedBasis.Bwd

type telescope = (Name.t * ty) bwd
val telescope : ty -> telescope * ty
val telescope_to_spine : telescope -> tm Tm.spine

val hole : telescope -> ty -> (tm Tm.cmd -> 'a m) -> 'a m
val define : telescope -> Name.t -> ty:ty -> tm -> unit m


(** Run this in a proof state to solve unification problems. *)
val ambulando : Name.t -> unit m

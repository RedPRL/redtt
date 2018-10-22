open Dev
open RedTT_Core
open Contextual

type rigidity = [`Rigid | `Flex]

type telescope = params
val telescope : ty -> telescope * ty
val telescope_to_spine : telescope -> tm Tm.spine

val push_guess : telescope -> ty0:ty -> ty1:ty -> tm -> tm m
val push_hole : rigidity -> telescope -> ty -> tm Tm.cmd m
val hole : rigidity -> telescope -> ty -> (tm Tm.cmd -> 'a m) -> 'a m

val user_define : telescope -> Name.t -> FileRes.filepath -> ResEnv.visibility -> [ `Transparent | `Opaque ] -> ty:ty -> tm -> unit m



val to_var : tm -> Name.t option

val abstract_ty : telescope -> ty -> ty
val abstract_tm : telescope -> tm -> tm

(** Run this in a proof state to solve unification problems. *)
val ambulando : unit m

val eval : tm -> NewDomain.con m

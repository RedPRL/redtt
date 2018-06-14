open Dev
open Contextual

type telescope = params
val telescope : ty -> telescope * ty
val telescope_to_spine : telescope -> tm Tm.spine

val push_guess : telescope -> ty0:ty -> ty1:ty -> tm -> tm m
val push_hole : [`Rigid | `Flex] -> telescope -> ty -> tm Tm.cmd m
val hole : [`Rigid | `Flex] -> telescope -> ty -> (tm Tm.cmd -> 'a m) -> 'a m

val define : telescope -> Name.t -> ty:ty -> tm -> unit m



val to_var : tm -> Name.t option

val abstract_ty : telescope -> ty -> ty
val abstract_tm : telescope -> tm -> tm

(** Run this in a proof state to solve unification problems. *)
val ambulando : unit m

module HSubst (T : Typing.S) :
sig
  val inst_ty_bnd : ty Tm.bnd -> Val.value * tm -> ty
  val (%%) : ty * tm -> tm Tm.frame -> ty * tm
end

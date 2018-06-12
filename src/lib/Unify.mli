open Dev
open Contextual

type telescope = params
val telescope : ty -> telescope * ty
val telescope_to_spine : telescope -> tm Tm.spine

val push_hole : telescope -> ty -> tm Tm.cmd m
val push_guess : telescope -> ty0:ty -> ty1:ty -> tm -> tm m

val hole : telescope -> ty -> (tm Tm.cmd -> 'a m) -> 'a m

val define : telescope -> Name.t -> ty:ty -> tm -> unit m



val to_var : tm -> Name.t option

val abstract_ty : telescope -> ty -> ty

(** Run this in a proof state to solve unification problems. *)
val ambulando : unit m

module HSubst (T : Typing.S) :
sig
  val inst_ty_bnd : ty Tm.bnd -> Val.value * tm -> ty
end

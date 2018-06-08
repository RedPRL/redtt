open Dev
open Contextual

type telescope = params
val telescope : ty -> telescope * ty
val telescope_to_spine : telescope -> tm Tm.spine
val pp_tele : telescope Pretty.t0

val hole : ?name:string option -> telescope -> ty -> (tm Tm.cmd -> 'a m) -> 'a m
val define : telescope -> Name.t -> ty:ty -> tm -> unit m
val guess : telescope -> ty0:ty -> ty1:ty -> tm -> (tm -> 'a m) -> 'a m


val to_var : tm -> Name.t option

val abstract_ty : telescope -> ty -> ty

(** Run this in a proof state to solve unification problems. *)
val ambulando : Name.t -> unit m

module HSubst (T : Typing.S) :
sig
  val inst_ty_bnd : ty Tm.bnd -> Val.value * tm -> ty
end

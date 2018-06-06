open Dev
open Contextual
open RedBasis.Bwd

type telescope = (Name.t * ty) bwd
val telescope : ty -> telescope * ty
val telescope_to_spine : telescope -> tm Tm.spine

val hole_named : Name.t -> telescope -> ty -> (tm Tm.cmd -> 'a m) -> 'a m
val hole : ?debug:string option -> telescope -> ty -> (tm Tm.cmd -> 'a m) -> 'a m
val define : telescope -> Name.t -> ty:ty -> tm -> unit m


val to_var : tm -> Name.t option
val pis : telescope -> ty -> ty

(** Run this in a proof state to solve unification problems. *)
val ambulando : Name.t -> unit m

module HSubst (T : Typing.S) :
sig
  val inst_ty_bnd : ty Tm.bnd -> Val.value * tm -> ty
end

include Monad.S

type tm = Tm.chk Tm.t 
type ty = Tm.chk Tm.t 
type rtm = ResEnv.t -> tm

type meta = Symbol.t

type hyp = string option * ty

type subgoal

(** Create a new subgoal, adding adding hypotheses to the local context *)
val subgoal : hyps:hyp list -> ty:ty -> subgoal

(** Get the current goal *)
val goal : ty m

(** Emit a new subgoal; this will cause the subgoal to be checked for well-formedness. This does not change focus. *)
val oblige : subgoal -> meta m

(** Fill the current hole; this will cause the supplied term to be typechecked. This does not change focus *)
val fill : tm -> unit m

(** Resolve the variables in the term according to the current hole's resolver environment. *)
val resolve : rtm -> tm m 

(** Move through the proof tree *)
val move : Tree.move -> unit m


module Notation :
sig
  (** Notation for 'subgoal' *)
  val (>-) : hyp list -> ty -> subgoal
end
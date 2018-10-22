open RedBasis.Bwd
open NewDomain

module QEnv :
sig
  type t

  val emp : unit -> t (* maybe just [emp : t]? *)

  (** [extend] gives you a new variable (in its level)
      and the new environment extended with that variable. *)
  val extend : t -> int * t

  val abs : Name.t bwd -> t -> t
  val abs1 : Name.t -> t -> t

  val ix_of_lvl : int -> t -> int
  val ix_of_atom : Name.t -> t -> int (* might throw Not_found *)
end

type qenv = QEnv.t

val quote_dim : qenv -> I.t -> Tm.tm

val equate_dim : qenv -> rel -> I.t -> I.t -> Tm.tm
(* favonia: whether these should take a value or con as arguments will hopefully be clear in the future. *)
val equate_con : qenv -> rel -> con -> con -> con -> Tm.tm
val equate_val : qenv -> rel -> con -> value -> value -> Tm.tm
val equate_neu : qenv -> rel -> neu -> neu -> Tm.tm
val equate_tycon : qenv -> rel -> con -> con -> Tm.tm
val equate_con_sys : qenv -> rel -> con -> con sys -> con sys -> (Tm.tm, Tm.tm) Tm.system

(* TODO: move to QEnv? *)
val extend : qenv -> value -> con * qenv

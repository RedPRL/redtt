open RedBasis.Bwd
open Domain

module Env :
sig
  type t

  val len : t -> int

  val emp : t
  val make : int -> t
  val succ : t -> t
  val abs : t -> Name.t bwd -> t

  val ix_of_lvl : int -> t -> int
  val ix_of_atom : Name.t -> t -> int
end

type env = Env.t

module Error : sig
  type t
  val pp : t Pretty.t0
  exception E of t
end

module type S =
sig
  val quote_nf : env -> nf -> Tm.tm
  val quote_neu : env -> neu -> Tm.tm Tm.cmd
  val quote_ty : env -> value -> Tm.tm

  val equiv : env -> ty:value -> value -> value -> unit
  val equiv_ty : env -> value -> value -> unit
  val subtype : env -> value -> value -> unit

end

module M (V : Val.S) : S

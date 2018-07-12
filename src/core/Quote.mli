open RedBasis.Bwd

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

module type S =
sig
  val quote_nf : env -> Val.nf -> Tm.tm
  val quote_neu : env -> Val.neu -> Tm.tm Tm.cmd
  val quote_ty : env -> Val.value -> Tm.tm

  val equiv : env -> ty:Val.value -> Val.value -> Val.value -> unit
  val equiv_ty : env -> Val.value -> Val.value -> unit
  val subtype : env -> Val.value -> Val.value -> unit

  module Error : sig
    type t
    val pp : t Pretty.t0
    exception E of t
  end
end

module M (V : Val.S) : S

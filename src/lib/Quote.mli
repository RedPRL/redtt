module Env :
sig
  type t

  val len : t -> int

  val emp : t
  val make : int -> t
  val succ : t -> t
  val abs : t -> Symbol.t list -> t

  val ix_of_lvl : int -> t -> int
  val ix_of_atom : Symbol.t -> t -> int
end

type env = Env.t

module type S =
sig
  val quote_nf : env -> Val.nf -> Tm.chk Tm.t
  val quote_neu : env -> Val.neu -> Tm.inf Tm.t
  val quote_ty : env -> Val.value -> Tm.chk Tm.t

  val quote_val_sys : env -> Val.value -> Val.val_sys -> Tm.chk Tm.t Tm.system

  val equiv : env -> ty:Val.value -> Val.value -> Val.value -> unit
  val equiv_ty : env -> Val.value -> Val.value -> unit
  val subtype : env -> Val.value -> Val.value -> unit
end

module M (V : Val.S) : S

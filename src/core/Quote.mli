open Domain

module Env :
sig
  type t

  val len : t -> int

  val emp : t
  val make : int -> t
  val succ : t -> t
  val abs : t -> Name.t list -> t

  val ix_of_lvl : int -> t -> int
  val ix_of_atom : Name.t -> t -> int
end

type env = Env.t

module Error : sig
  type t
  val pp : t Pp.t0
  exception E of t
end

module type S =
sig
  val quote_nf : env -> nf -> Tm.tm
  val quote_neu : env -> neu -> Tm.tm Tm.cmd
  val quote_ty : env -> value -> Tm.tm
  val quote_val_sys : env -> value -> val_sys -> (Tm.tm, Tm.tm) Tm.system
  val equate_data_params : env -> Name.t -> Desc.body -> env_el list -> env_el list -> Tm.tm list
  val quote_data_params : env -> Name.t -> Desc.body -> env_el list -> Tm.tm list

  val quote_dim : env -> I.t -> Tm.tm

  val equiv : env -> ty:value -> value -> value -> unit
  val equiv_ty : env -> value -> value -> unit
  val equiv_dim : env -> I.t -> I.t -> unit
  val equiv_data_params : env -> Name.t -> Desc.body -> env_el list -> env_el list -> unit
  val subtype : env -> value -> value -> unit

  val approx_restriction : env -> value -> value -> val_sys -> val_sys -> unit

end

module M (V : Val.S) : S

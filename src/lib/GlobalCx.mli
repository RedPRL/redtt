type t

val emp : t
val define : t -> string -> ty:Tm.chk Tm.t -> tm:Tm.chk Tm.t -> t
val add_hole : t -> string -> ty:Tm.chk Tm.t -> sys:Tm.chk Tm.t Tm.system -> t

module M (Sig : sig val globals : t end) : Val.Sig

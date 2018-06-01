type t

val emp : t
val define : t -> Name.t -> ty:Tm.tm -> tm:Tm.tm -> t
val ext : t -> Name.t -> ty:Tm.tm -> sys:(Tm.tm, Tm.tm) Tm.system -> t

val lookup_ty : t -> Name.t -> Tm.twin -> Tm.tm

val merge : t -> t -> t

module M (Sig : sig val globals : t end) : Val.Sig

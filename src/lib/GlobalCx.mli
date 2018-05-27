type t

val emp : t
val define : t -> Name.t -> ty:Tm.tm -> tm:Tm.tm -> t
val add_hole : t -> Name.t -> ty:Tm.tm -> sys:(Tm.tm, Tm.tm) Tm.system -> t

val lookup_ty : t -> Name.t -> Tm.twin -> Tm.tm

module M (Sig : sig val globals : t end) : Val.Sig

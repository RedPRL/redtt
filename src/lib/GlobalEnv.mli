type t

type 'a param =
  [ `P of 'a
  | `Tw of 'a * 'a
  ]

type entry = {ty : Tm.tm; sys : (Tm.tm, Tm.tm) Tm.system}

val emp : t
val define : t -> Name.t -> ty:Tm.tm -> tm:Tm.tm -> t
val ext : t -> Name.t -> entry param -> t
val lookup_ty : t -> Name.t -> Tm.twin -> Tm.tm

val restrict : Tm.tm -> Tm.tm -> t -> t

val restriction : t -> Restriction.t


val pp : t Pretty.t0

module M (Sig : sig val globals : t end) : Val.Sig

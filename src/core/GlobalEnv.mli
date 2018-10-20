type t

type ty = Tm.tm
type tm = Tm.tm

type entry =
  [ `P of ty
  | `Def of ty * tm
  | `Tw of ty * ty
  | `I
  | `Desc of Desc.desc
  ]

val emp : unit -> t
val define : t -> Name.t -> ty:Tm.tm -> tm:Tm.tm -> t
val ext : t -> Name.t -> entry -> t
val ext_meta : t -> Name.t -> entry -> t
val ext_dim : t -> Name.t -> t
val restrict : Tm.tm -> Tm.tm -> t -> t


val declare_datatype : Name.t -> Desc.desc -> t -> t
val replace_datatype : Name.t -> Desc.desc -> t -> t (* [Not_found] if the datatype is not there *)
val lookup_datatype : t -> Name.t -> Desc.desc

module T : module type of (Map.Make (Name))

val global_dims : t -> I.t T.t


val lookup_ty : t -> Name.t -> Tm.twin -> Tm.tm
val lookup : t -> Name.t -> entry
val lookup_with_twin : t -> Name.t -> Tm.twin -> Tm.tm * Tm.tm option

val restriction : t -> Restriction.t


val pp : t Pp.t0

module M (Sig : sig val globals : t end) : Val.Sig

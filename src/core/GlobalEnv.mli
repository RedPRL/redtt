type t

type ty = Tm.tm
type tm = Tm.tm

type entry =
  [ `P of ty
  | `Def of ty * tm
  | `Tw of ty * ty
  | `Tick
  | `I
  ]

val emp : unit -> t
val define : t -> Name.t -> ty:Tm.tm -> tm:Tm.tm -> t
val ext : t -> Name.t -> entry -> t
val ext_meta : t -> Name.t -> entry -> t
val ext_dim : t -> Name.t -> t
val ext_tick : t -> Name.t -> t
val restrict : Tm.tm -> Tm.tm -> t -> t
val kill_from_tick : t -> Name.t -> t


val declare_datatype : Desc.data_label -> (Tm.tm, Tm.tm) Desc.desc -> t -> t
val lookup_datatype : Desc.data_label -> t -> (Tm.tm, Tm.tm) Desc.desc

module T : module type of (Map.Make (Name))

val global_dims : t -> I.t T.t


val lookup_ty : t -> Name.t -> Tm.twin -> Tm.tm
val lookup : t -> Name.t -> entry

val restriction : t -> Restriction.t


val pp : t Pp.t0

module M (Sig : sig val globals : t end) : Val.Sig

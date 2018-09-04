type t

type 'a param =
  [ `P of 'a
  | `Tw of 'a * 'a
  | `Tick
  | `I
  ]

type entry = {ty : Tm.tm; sys : (Tm.tm, Tm.tm) Tm.system}

val emp : unit -> t
val define : t -> Name.t -> ty:Tm.tm -> tm:Tm.tm -> t
val ext : t -> Name.t -> entry param -> t
val ext_meta : t -> Name.t -> entry param -> t
val ext_dim : t -> Name.t -> t
val ext_tick : t -> Name.t -> t
val restrict : Tm.tm -> Tm.tm -> t -> t
val kill_from_tick : t -> Name.t -> t


val declare_datatype : Desc.data_label -> Tm.NewDesc.pdesc -> t -> t
val lookup_datatype : Desc.data_label -> t -> Tm.NewDesc.pdesc

module T : module type of (Map.Make (Name))

val global_dims : t -> I.t T.t


val lookup_ty : t -> Name.t -> Tm.twin -> Tm.tm
val lookup_kind : t -> Name.t -> unit param

val restriction : t -> Restriction.t


val pp : t Pp.t0

module M (Sig : sig val globals : t end) : Val.Sig

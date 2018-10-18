open RedTT_Core

(** This module has two responsibilities:

    1. maintain the mapping from strings to names.
    2. keep track of items to be serialized. *)

type resolution =
  [ `Ix of int
  | `Var of Name.t
  | `Metavar of Name.t
  | `Datatype of Name.t
  ]

type visibility =
  [ `Private | `Public ]


type t
val init : unit -> t
val bind : string -> t -> t
val bindn : string list -> t -> t
val bind_opt : string option -> t -> t

val register_var : visibility:visibility -> Name.t -> t -> t
val register_metavar : visibility:visibility -> Name.t -> t -> t
val register_datatype : visibility:visibility -> Name.t -> t -> t

val import_globals : visibility:visibility -> t -> t -> t

val get : string -> t -> resolution
val get_from_idx : int -> t -> resolution
val idx_of_name_opt : Name.t -> t -> int option

val pp_visibility : visibility Pp.t0

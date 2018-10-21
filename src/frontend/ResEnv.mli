open RedTT_Core

(** This module has two responsibilities:

    1. maintain the mapping from strings to names.
    2. keep track of items to be serialized. *)

type resolution =
  [ `Ix of int
  | `Name of Name.t
  ]

type visibility =
  [ `Private | `Public ]


type t
val init : unit -> t
val bind : string -> t -> t
val bindn : string list -> t -> t
val bind_opt : string option -> t -> t

val register_name : visibility:visibility -> Name.t -> t -> t

val import_globals : visibility:visibility -> t -> t -> t

val get : string -> t -> resolution
val get_name : string -> t -> Name.t

val id_of_name : Name.t -> t -> int option
val export_native_globals : t -> (string option * Name.t) list

val pp_visibility : visibility Pp.t0

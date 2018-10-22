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

val add_native_global : visibility:visibility -> Name.t -> t -> t

val import_globals : visibility:visibility -> t -> t -> t

val get : string -> t -> resolution
val get_name : string -> t -> Name.t


val native_of_name : Name.t -> t -> int option
val name_of_native : int -> t -> Name.t option
type exported_natives = (string option * Name.t) list
type exported_foreigners = (string * Name.t) list
val export_native_globals : t -> exported_natives
val export_foreign_globals : t -> exported_foreigners
val reconstruct : exported_foreigners -> exported_natives -> t

val pp_visibility : visibility Pp.t0

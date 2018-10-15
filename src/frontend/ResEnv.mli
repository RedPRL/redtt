open RedTT_Core

type resolution =
  [ `Ix of int
  | `Var of Name.t
  | `Metavar of Name.t
  | `Datatype of string
  ]

type visibility =
  [ `Private | `Public ]


type t
val init : unit -> t
val bind : string -> t -> t
val bindn : string list -> t -> t
val bind_opt : string option -> t -> t

val named_var : ?visibility:visibility -> string -> Name.t -> t -> t
val named_metavar : ?visibility:visibility -> string -> Name.t -> t -> t
val datatype : ?visibility:visibility -> string -> t -> t

val import_globals : ?visibility:visibility -> t -> t -> t

val get : string -> t -> resolution

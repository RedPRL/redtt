type resolution =
  [ `Ix of int
  | `Var of Name.t
  | `Metavar of Name.t
  | `Datatype of string
  ]


type t
val init : unit -> t
val bind : string -> t -> t
val bindn : string list -> t -> t
val bind_opt : string option -> t -> t

val named_var : string -> Name.t -> t -> t
val named_metavar : string -> Name.t -> t -> t
val datatype : string -> t -> t

val get : string -> t -> resolution

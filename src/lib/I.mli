type atom = Name.t

type 'a f =
  [ `Dim0
  | `Dim1
  | `Atom of 'a
  ]

val map : ('a -> 'b) -> 'a f -> 'b f
val bind : 'a f -> ('a -> 'b f) -> 'b f




type t = atom f

type action
val idn : action
val swap : atom -> atom -> action
val subst : t -> atom -> action
val cmp : action -> action -> action

val equate : t -> t -> action

val act : action -> t -> t

type compare =
  [ `Same
  | `Apart
  | `Indet
  ]

val compare : t -> t -> compare


val pp : t Pretty.t0


exception Inconsistent

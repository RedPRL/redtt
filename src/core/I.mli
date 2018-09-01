open RedBasis.Bwd

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

val occurs_in_action : atom bwd -> action -> bool


val act : action -> t -> t

type compare =
  [ `Same
  | `Apart
  | `Indet
  ]

val compare : t -> t -> compare

val absent : atom -> t -> bool


val pp : t Pp.t0
val pp_action : action Pp.t0


exception Inconsistent

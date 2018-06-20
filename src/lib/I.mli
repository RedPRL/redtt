type atom = Name.t

type t =
  [ `Dim0
  | `Dim1
  | `Atom of atom
  ]

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

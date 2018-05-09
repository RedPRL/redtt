type atom = Symbol.t
type t
val dim0 : t
val dim1 : t
val named : atom -> t

type compare =
  | Same
  | Apart
  | Indeterminate

val compare : t -> t -> compare

val unleash : t -> [`Dim0 | `Dim1 | `Generic ]


type action
val subst : t -> atom -> action
val equate : t -> t -> action
val swap : atom -> atom -> action
val cmp : action -> action -> action
val idn : action

val act : action -> t -> t

type atom = Symbol.t

type repr =
  | Dim0
  | Dim1
  | Atom of atom

type t

val dim0 : t
val dim1 : t
val named : atom -> t

val entangle : t -> t -> t * t

type compare =
  | Same
  | Apart
  | Indeterminate

val compare : t -> t -> compare

type action
val subst : t -> atom -> action
val equate : t -> t -> action
val swap : atom -> atom -> action
val cmp : action -> action -> action
val idn : action

val action_is_id : action -> bool

val act : action -> t -> t

val unleash : t -> repr

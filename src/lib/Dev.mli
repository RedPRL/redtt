type tm = Tm.chk Tm.t
type ty = Tm.chk Tm.t
type name = string option

type boundary = Tm.chk Tm.t Tm.system
type rty = {ty : ty; sys : boundary}

(** A [cell] is an entry in the development context, what Conor McBride called a {e component} in his thesis.
    These cells are also the left parts of the "binders" in the development calculus.
*)
type cell =
  | Guess of {nm : name; ty : rty; guess : dev}
  | Let of {nm : name; ty : ty; def : tm}
  | Lam of {nm : name; ty : ty}

and dev =
  | Hole of rty
  | Node of cell * dev
  | Ret of tm

val subst : Tm.subst -> dev -> dev

val pp_dev : dev Pretty.t
val pp_cell : cell Pretty.t
val ppenv_cell : Pretty.env -> cell -> Pretty.env

val extract : dev -> tm

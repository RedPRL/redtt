type ty = Tm.tm
type tm = Tm.tm

type 'a dev_view =
  | Ret of tm
  | Hole of ty
  | Node of 'a cell_view * 'a

and 'a cell_view =
  | Lam of {x : Name.t; ty : ty}
  | Guess of {x : Name.t; ty : ty; guess : 'a}
  | Let of {x : Name.t; ty : ty; tm : tm}

type dev

val make : dev dev_view -> dev
val unleash : dev -> dev dev_view


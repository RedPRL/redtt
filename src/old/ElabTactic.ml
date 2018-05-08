type tactic = unit ElabMonad.m
type name = string option

module E = ElabMonad
module Notation = Monad.Notation (E)
open E.Notation
open Notation

exception NotApplicable

let under tac =
  E.move0 `Down >>
  E.move (`Star `Right) >>
  tac >>
  E.move0 `Up


module Pi =
struct
  let intro nm : unit E.m =
    E.goal >>= fun ty ->
    match Tm.out ty with
    | Tm.Pi (dom, Tm.B (_, cod)) ->
      E.oblige ([nm, dom] >- cod) >>= fun alpha ->
      E.fill @@ Tm.lam nm @@ Tm.up @@ Tm.meta alpha @@ Tm.inst0 @@ Tm.var 0

    | _ ->
      raise NotApplicable

  let formation nm : unit E.m =
    E.goal >>= fun ty ->
    match Tm.out ty with
    | Tm.Univ lvl ->
      E.oblige ([] >- Tm.univ lvl) >>= fun alpha ->
      let dom = Tm.up @@ Tm.meta alpha Tm.Id in
      E.oblige ([nm, dom] >- Tm.univ lvl) >>= fun beta ->
      let cod = Tm.up @@ Tm.meta beta @@ Tm.inst0 @@ Tm.var 0 in
      E.fill @@ Tm.pi nm dom cod

    | _ ->
      raise NotApplicable
end

module Sg =
struct
  let formation nm =
    E.goal >>= fun ty ->
    match Tm.out ty with
    | Tm.Univ lvl ->
      E.oblige ([] >- Tm.univ lvl) >>= fun alpha ->
      let dom = Tm.up @@ Tm.meta alpha Tm.Id in
      E.oblige ([nm, dom] >- Tm.univ lvl) >>= fun beta ->
      let cod = Tm.up @@ Tm.meta beta @@ Tm.inst0 @@ Tm.var 0 in
      E.fill @@ Tm.sg nm dom cod

    | _ ->
      raise NotApplicable

  let intro =
    E.goal >>= fun ty ->
    match Tm.out ty with
    | Tm.Sg (dom, Tm.B (nm, cod)) ->
      E.oblige ([] >- dom) >>= fun alpha ->
      let tm0 = Tm.meta alpha Tm.Id in
      let cod' = Tm.let_ nm tm0 cod in
      E.oblige ([] >- cod') >>= fun beta ->
      let tm1 = Tm.meta beta Tm.Id in
      E.fill @@ Tm.cons (Tm.up tm0) (Tm.up tm1)

    | _ ->
      raise NotApplicable

end

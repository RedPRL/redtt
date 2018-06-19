type t =
  | Dim0
  | Dim1
  | Atom of Name.t

type action =
  | Subst of t * Name.t
  | Swap of Name.t * Name.t
  | Idn
  | Cmp of action * action

exception Inconsistent

let equate r0 r1 =
  match r0, r1 with
  | Dim0, Dim0 ->
    Idn
  | Dim1, Dim1 ->
    Idn
  | Dim0, Dim1 ->
    raise Inconsistent
  | Dim1, Dim0 ->
    raise Inconsistent
  | Atom a, (Dim0 | Dim1) ->
    Subst (r1, a)
  | (Dim0 | Dim1), Atom a ->
    Subst (r0, a)
  | Atom a, Atom b when a < b ->
    Subst (r0, b)
  | Atom a, Atom b when a > b ->
    Subst (r1, a)
  | Atom _, Atom _ ->
    Idn

let rec act phi =
  function
  | (Dim0 | Dim1) as r -> r
  | Atom a as r ->
    match phi with
    | Idn -> r
    | Swap (b, c) when a = b -> Atom c
    | Swap (b, c) when a = c -> Atom b
    | Subst (s, b) when a = b -> s
    | Cmp (psi1, psi0) -> act psi1 @@ act psi0 r
    | _ -> r




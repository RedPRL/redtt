type atom = Symbol.t

type t =
  | Dim0
  | Dim1
  | Atom of {atom : atom; history : atom list}

(* The [Atom] constructor is the only weird case. It is implemented this way in order to
   support diagonal equations, which we treat as different from the substitution of one
   dimension for an atom. In the case of a diagonal x=y, we generate a fresh atom 'z',
   and then replace both and y with z; except, using the [history] field, we remember that
   each one used to be x or y.

   When comparing generic dimensions, only the [atom] field is considered; but using the history,
   we can reconstruct the 'real' name of the dimension, which is crucial for quotation. *)

let dim0 = Dim0
let dim1 = Dim1
let named x = Atom {atom = x; history = []}

type action =
  | Subst of t * atom
  | Swap of atom * atom
  | Diag of atom * (atom * atom)
  | Cmp of action * action
  | Id

let subst r x = Subst (r, x)

let equate r r' =
  match r, r' with
  | Dim0, Dim0 ->
    Id
  | Dim1, Dim1 ->
    Id
  | Dim0, Atom atm ->
    subst Dim0 atm.atom
  | Dim1, Atom atm ->
    subst Dim1 atm.atom
  | Atom atm, Dim0 ->
    subst Dim0 atm.atom
  | Atom atm, Dim1 ->
    subst Dim1 atm.atom
  | Atom atm0, Atom atm1 ->
    let z = Symbol.fresh () in
    Diag (z, (atm0.atom, atm1.atom))
  | _ ->
    failwith "Inconsistent equation"

let unleash r =
  match r with
  | Dim0 -> `Dim0
  | Dim1 -> `Dim1
  | _ -> `Generic

let cmp sigma1 sigma0 =
  Cmp (sigma1, sigma0)

let idn = Id

let swap x y =
  Swap (x, y)

type compare =
  | Same
  | Apart
  | Indeterminate

let compare r r' =
  match r, r' with
  | Dim0, Dim0 -> Same
  | Dim1, Dim1 -> Same
  | Dim0, Dim1 -> Apart
  | Dim1, Dim0 -> Apart
  | Atom atm0, Atom atm1 ->
    if atm0.atom = atm1.atom then
      Same
    else
      Indeterminate
  | _ -> Indeterminate

let atom_swap (x, y) z =
  if x = z then y else if y = z then x else z

let rec act sigma r =
  match r, sigma with
  | (Dim0 | Dim1), _ -> r
  | _, Id -> r
  | _, Cmp (sigma1, sigma0) ->
    act sigma1 @@ act sigma0 r
  | Atom atm, Subst (r', x) ->
    if atm.atom = x then r' else r
  | Atom atm, Diag (z, (x, y)) ->
    if atm.atom = x then
      Atom {atom = z; history = x :: atm.history}
    else if atm.atom = y then
      Atom {atom = z; history = y :: atm.history}
    else
      r
  | Atom atm, Swap (x, y) ->
    Atom
      {atom = atom_swap (x, y) atm.atom;
       history = List.map (atom_swap (x, y)) atm.history}


exception ExpectedAtom

let atom r =
  match r with
  | Atom atm ->
    atm.atom
  | _ ->
    raise ExpectedAtom

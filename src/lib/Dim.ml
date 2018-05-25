type atom = Name.t

type repr =
  | Dim0
  | Dim1
  | Atom of atom

module Repr =
struct
  type t = repr
  let compare = Pervasives.compare
end

module S = Set.Make (Repr)

type t = repr * S.t

let singleton r = r, S.singleton r
let from_reprs r rs = r, S.of_list rs

let dim0 = singleton Dim0
let dim1 = singleton Dim1
let named a = singleton @@ Atom a

type compare =
  | Same
  | Apart
  | Indeterminate

let compare_repr r r' =
  match r, r' with
  | Dim0, Dim0 -> Same
  | Dim1, Dim1 -> Same
  | Dim1, Dim0 -> Apart
  | Dim0, Dim1 -> Apart
  | Atom x, Atom y ->
    if x = y then Same else Indeterminate
  | _ -> Indeterminate


let compare (_, r) (_, r') =
  if S.mem Dim0 r && S.mem Dim0 r' then Same
  else if S.mem Dim1 r && S.mem Dim1 r' then Same
  else if S.mem Dim0 r && S.mem Dim1 r' then Apart
  else if S.mem Dim1 r && S.mem Dim0 r' then Apart
  else if S.is_empty @@ S.inter r r' then Indeterminate
  else Same

let entangle (r, rs) (r', rs') =
  let rs'' = S.union rs rs' in
  (r, rs''), (r', rs'')




type action =
  | Subst of t * atom
  | Swap of atom * atom
  | UnionIfIntersects of S.t
  | Cmp of action * action
  | Id

let subst r x = Subst (r, x)

let equate t t' =
  let _, rs = t in
  let _, rs' = t' in
  UnionIfIntersects (S.union rs rs')

let swap x y = Swap (x, y)

let cmp phi psi = Cmp (phi, psi)

let idn = Id


let swap_repr x y rep =
  match rep with
  | Dim0 -> Dim0
  | Dim1 -> Dim1
  | Atom z ->
    Atom (if x = z then y else if y = z then x else z)


let rec act phi t =
  match phi with
  | Id -> t

  | Swap (x, y) ->
    let r, rs = t in
    swap_repr x y r, S.map (swap_repr x y) rs

  | Cmp (phi1, phi0) ->
    act phi1 @@ act phi0 t

  | UnionIfIntersects rs' ->
    let r, rs = t in
    if S.is_empty @@ S.inter rs rs' then t else
      r, S.union rs rs'

  | Subst (t', x) ->
    begin
      match t with
      | Atom y, _ ->
        if x = y then t' else t
      | _ -> t
    end

let unleash (r, _) = r

let action_is_id phi =
  match phi with
  | Id -> true
  | _ -> false

let pp_repr fmt r =
  match r with
  | Dim0 ->
    Format.fprintf fmt "0"
  | Dim1 ->
    Format.fprintf fmt "1"
  | Atom x ->
    Uuseg_string.pp_utf_8 fmt @@
    Name.to_string x

let pp_repr_set fmt rs =
  let comma fmt () = Format.fprintf fmt ", " in
  Format.pp_print_list ~pp_sep:comma pp_repr fmt @@ S.elements rs

let pp fmt (r, rs) =
  Format.fprintf fmt "@[<1>{%a|%a}@]" pp_repr r pp_repr_set rs

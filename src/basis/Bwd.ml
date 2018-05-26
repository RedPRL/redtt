type 'a bwd =
  | Emp
  | Snoc of 'a bwd * 'a

module BwdNotation =
struct
  let (#<) xs x =
    Snoc (xs, x)

  let rec (<.>) xs ys =
    match ys with
    | Emp -> xs
    | Snoc (ys, y) ->
      Snoc (xs <.> ys, y)


  let rec (<><) xs ys =
    match ys with
    | [] -> xs
    | y :: ys -> (xs #< y) <>< ys

  let rec (<>>) xs ys =
    match xs with
    | Emp -> ys
    | Snoc (xs, x) -> xs <>> x :: ys
end

module Bwd =
struct
  open BwdNotation

  let rec map f xs =
    match xs with
    | Emp -> Emp
    | Snoc (xs, x) -> Snoc (map f xs, f x)

  let to_list xs =
    xs <>> []

  let from_list xs =
    Emp <>< xs
end

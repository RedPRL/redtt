type 'a bwd =
  | Emp
  | Snoc of 'a bwd * 'a

module Notation =
struct
  let (#<) xs x =
    Snoc (xs, x)


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
  open Notation

  let to_list xs =
    xs <>> []

  let from_list xs =
    Emp <>< xs
end

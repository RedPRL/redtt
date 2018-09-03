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

  let rec nth xs i =
    match xs with
    | Emp ->
      failwith "Bwd.nth"
    | Snoc (_, x) when i = 0 -> x
    | Snoc (xs, _) -> nth xs @@ i - 1

  let rec mem a xs =
    match xs with
    | Emp -> false
    | Snoc (xs, x) ->
      if a = x then true else mem a xs

  let rec length =
    function
    | Emp -> 0
    | Snoc (xs, _) ->
      1 + length xs

  let rec map f =
    function
    | Emp -> Emp
    | Snoc (xs, x) -> Snoc (map f xs, f x)

  let mapi f =
    let rec go i =
      function
      | Emp -> Emp
      | Snoc (xs, x) -> Snoc (go (i + 1) xs, f i x)
    in
    go 0

  let rec flat_map f =
    function
    | Emp -> Emp
    | Snoc (xs, x) -> flat_map f xs <>< f x

  let rec filter f =
    function
    | Emp -> Emp
    | Snoc (xs, x) ->
      let xs' = filter f xs in
      if f x then Snoc (xs', x) else xs'

  let to_list xs =
    xs <>> []

  let from_list xs =
    Emp <>< xs

  let rev xs = from_list @@ List.rev @@ to_list xs
end

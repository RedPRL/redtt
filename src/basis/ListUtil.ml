let rec split n xs =
  match n, xs with
  | 0, _ ->
    [], xs
  | n, x :: xs ->
    let ys, zs = split (n - 1) xs in
    x :: ys, zs
  | _ ->
    failwith "ListUtil.take"

let rec flat_map f xs =
  match xs with
  | [] -> []
  | x :: xs ->
    f x @ flat_map f xs

let rec index_of pred xs =
  match xs with
  | [] ->
    failwith "index_of: not found"
  | x :: _ when pred x ->
    0
  | _ :: xs ->
    1 + index_of pred xs


let rec map3 f xs ys zs =
  match xs, ys, zs with
  | [], [], [] ->
    []
  | x :: xs, y :: ys, z :: zs ->
    f x y z :: map3 f xs ys zs
  | _ ->
    failwith "map3: length mismatch"

let tabulate n f =
  let rec go i =
    if i == n then [] else
      f i :: go (i+1)
  in
  go 0

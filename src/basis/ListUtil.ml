let rec split n xs =
  match n, xs with
  | 0, _ ->
    [], xs
  | n, x :: xs ->
    let ys, zs = split (n - 1) xs in
    x :: ys, zs
  | _ ->
    failwith "ListUtil.take"

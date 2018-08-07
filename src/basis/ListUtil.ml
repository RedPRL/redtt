let rec split n xs =
  match n, xs with
  | 0, _ ->
    [], xs
  | n, x :: xs ->
    let ys, zs = split (n - 1) xs in
    x :: ys, zs
  | _ ->
    failwith "ListUtil.take"

let rec index_of pred xs =
  match xs with
  | [] ->
    failwith "index_of: not found"
  | x :: _ when pred x ->
    0
  | _ :: xs ->
    1 + index_of pred xs

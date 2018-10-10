let is_nil =
  function
  | [] -> true
  | _ -> false

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


let rec split_last l =
  match l with
  | [] -> failwith "split_last: empty list"
  | [x] -> ([], x)
  | x :: y :: ys ->
    let zs, z = split_last (y :: ys) in
    x :: zs, z

let split_head l =
  match l with
  | [] -> failwith "split_head_append: empty list"
  | x :: xs -> x, xs


let rec filter_map f xs =
  match xs with
  | [] -> []
  | x :: xs ->
    match f x with
    | Some y -> y :: filter_map f xs
    | None -> filter_map f xs

let rec find_map_opt f xs =
  match xs with
  | [] -> None
  | x :: xs ->
    match f x with
    | Some y -> Some y
    | None -> find_map_opt f xs

let foreach l f = List.map f l
let foreach2 l0 l1 f = List.map2 f l0 l1

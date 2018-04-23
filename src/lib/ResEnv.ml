type t = string option list

let init = []
let bind x env = Some x :: env
let bind_opt x env = x :: env

let rec get x env =
  match env with 
  | [] ->
    failwith @@ "variable not found: " ^ x
  | Some y :: ys ->
    if x = y 
    then 0
    else 1 + get x ys
  | None :: ys ->
    1 + get x ys 
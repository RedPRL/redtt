type t = string list

let init = []
let bind x env = x :: env
let rec get x env =
  match env with 
  | [] ->
    failwith @@ "variable not found: " ^ x
  | y :: ys ->
    if x = y 
    then 0
    else 1 + get x ys
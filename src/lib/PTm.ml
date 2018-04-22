module type ResEnv =
sig
  type t
  val init : t
  val bind : string -> t -> t
  val get : string -> t -> int
end

module ResEnv : ResEnv = 
struct
  type t = string list

  let init = []
  let bind x env = x :: env
  let rec get x env =
    match env with 
    | [] ->
      failwith "variable not found"
    | y :: ys ->
      if x = y 
      then 0
      else 1 + get x ys
end
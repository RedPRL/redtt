type ('x, 'a) f = 
  | Id
  | Keep of 'a
  | Skip of 'a
  | Sub of 'a * 'x
  | Cmp of 'a * 'a

type 'x t = {node : ('x, 'x t) f }
type t0 = Void.t t

let id = {node = Id}
let keep t = {node = Keep t}
let skip t = {node = Skip t}
let sub t a = {node = Sub (t, a)}

let cmp t1 t2 = {node = Cmp (t1, t2)}

let rec act f xs =
  match f.node, xs with 
  | Id, _ -> xs
  | Keep f, x::xs -> x :: act f xs
  | Skip f, _::xs -> act f xs
  | Sub (_, void), _ -> Void.abort void
  | Cmp (g, f), _ -> act g (act f xs)
  | _ -> failwith "Thin.act: invalid arguments"

(* TODO: more efficient version possible *)
let proj f xs = 
  List.hd @@ act f xs
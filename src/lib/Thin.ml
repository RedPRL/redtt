type 'a f = 
  | Id
  | Keep of 'a
  | Skip of 'a
  | Cmp of 'a * 'a

type t = {node : t f }
let into tf = {node = tf}

let id = into Id
let keep t = into @@ Keep t
let skip t = into @@ Skip t
let cmp t1 t2 = into @@ Cmp (t1, t2)


let rec act f xs =
  match f.node, xs with 
  | Id, _ -> xs
  | Keep f, x::xs -> x :: act f xs
  | Skip f, _::xs -> act f xs
  | Cmp (g, f), _ -> act g (act f xs)
  | _ -> failwith "Thin.act: invalid arguments"

(* TODO: more efficient version possible *)
let proj f xs = 
  List.hd @@ act f xs
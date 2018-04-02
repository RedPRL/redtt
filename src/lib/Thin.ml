type ('x, 'a) f = 
  | Id
  | Keep of 'a
  | Skip of 'a
  | Sub of 'a * 'x
  | Cmp of 'a * 'a

type 'x t = {node : ('x, 'x t) f }
let into tf = {node = tf}

type t0 = Void.t t

let id = into Id
let keep t = into @@ Keep t
let skip t = into @@ Skip t
let sub t a = into @@ Sub (t, a)
let cmp t1 t2 = into @@ Cmp (t1, t2)


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


module Ix =
struct
  type 'a r = V of int | R of 'a

  let rec proj (ih : 'a t -> 'a -> 'a) f i = 
    match f.node, i with
    | Id, _ -> V i
    | Keep f, 0 -> V 0
    | Keep f, _ ->
      begin
        match proj ih f (i - 1) with 
        | V j -> V (j + 1)
        | R a -> R (ih (skip id) a)
      end
    | Skip f, i -> proj ih f (i + 1)
    | Sub (f, a), 0 -> R a
    | Sub (f, a), _ -> proj ih f (i - 1)
    | Cmp (g, f), _ ->
      begin
        match proj ih f i with 
        | V j -> proj ih g j
        | R a -> R (ih g a)
      end

  let rec proj0 f i = 
    match f.node, i with
    | Id, _ -> i
    | Keep f, 0 -> 0
    | Keep f, _ -> 1 + proj0 f (i - 1)
    | Skip f, i -> proj0 f (i + 1)
    | Sub (f, a), _ -> Void.abort a
    | Cmp (g, f), _ -> proj0 g (proj0 f i)


  let rec from_ix i = 
    match i with 
    | 0 -> id
    | _ -> skip (from_ix (i - 1))

  let to_ix f = proj0 f 0

end

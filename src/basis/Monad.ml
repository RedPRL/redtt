module type S =
sig
  type 'a m
  val bind : 'a m -> ('a -> 'b m) -> 'b m
  val try_ : 'a m -> (exn -> 'a m) -> 'a m
  val ret : 'a -> 'a m
end

module type Notation =
sig
  type 'a m

  val (>>=) : 'a m -> ('a -> 'b m) -> 'b m
  val (>>) : 'a m -> 'b m -> 'b m
  val (<@>>) : ('a -> 'b) -> 'a m -> 'b m
  val (<<@>) : 'a m -> ('a -> 'b) -> 'b m
  val (<*>) : ('a -> 'b) m -> 'a m -> 'b m
  val (<&>) : 'a m -> 'b m -> ('a * 'b) m
  val (<||) : bool m -> unit m -> unit m
end

module Notation (M : S)  : Notation with type 'a m := 'a M.m =
struct
  let (>>=) = M.bind
  let (>>) m n =
    m >>= fun _ -> n

  let (<@>>) f m =
    m >>= fun x ->
    M.ret @@ f x

  let (<<@>) m f = f <@>> m

  let (<*>) m n =
    m >>= fun f ->
    f <@>> n

  let (<&>) m n =
    m >>= fun x ->
    n >>= fun y ->
    M.ret (x, y)

  let (<||) a b =
    a >>= fun x ->
    if x then M.ret () else b
end

module Util (M : S) =
struct
  module N = Notation (M)
  open N

  let rec traverse f =
    function
    | [] -> M.ret []
    | x::xs ->
      f x >>= fun y ->
      traverse f xs >>= fun ys ->
      M.ret @@ y :: ys

  let rec fold_left f acc xs =
    match xs with
    | [] ->
      M.ret acc
    | x :: xs ->
      f acc x >>= fun a ->
      fold_left f a xs

  let rec iter f xs =
    match xs with
    | [] ->
      M.ret ()
    | x :: xs ->
      f x >> iter f xs

end

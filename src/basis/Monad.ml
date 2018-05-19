module type S =
sig
  type 'a m
  val bind : 'a m -> ('a -> 'b m) -> 'b m
  val ret : 'a -> 'a m
end

module type Notation =
sig
  type 'a m

  val (>>=) : 'a m -> ('a -> 'b m) -> 'b m
  val (>>) : 'a m -> 'b m -> 'b m
  val (<$>) : ('a -> 'b) -> 'a m -> 'b m
end

module Notation (M : S) =
struct
  let (>>=) = M.bind
  let (>>) m n =
    m >>= fun _ -> n

  let (<$>) f m =
    m >>= fun x ->
    M.ret @@ f x
end

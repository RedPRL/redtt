module type S =
sig
  type t
  type 'a m
  val act : Dim.action -> t -> t m
end

module type S' =
sig
  type t
  type 'a m
  val act : I.action -> t -> t m
end

module Prod (X1 : S with type 'a m = 'a) (X2 : S with type 'a m = 'a) : S with type t = X1.t * X2.t with type 'a m = 'a =
struct
  type t = X1.t * X2.t
  type 'a m = 'a

  let act phi (x1, x2) =
    X1.act phi x1, X2.act phi x2
end

module Prod' (X1 : S' with type 'a m = 'a) (X2 : S' with type 'a m = 'a) : S' with type t = X1.t * X2.t with type 'a m = 'a =
struct
  type t = X1.t * X2.t
  type 'a m = 'a

  let act phi (x1, x2) =
    X1.act phi x1, X2.act phi x2
end

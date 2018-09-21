module type S =
sig
  type t

  val open_var : int -> Name.t -> t -> t
  val close_var : Name.t -> int -> t -> t
end

module List (M : S) : S with type t = M.t list =
struct
  type t = M.t list

  let open_var i a = List.map @@ M.open_var i a
  let close_var a i = List.map @@ M.close_var a i
end

module Pair (M0 : S) (M1 : S) : S with type t = M0.t * M1.t =
struct
  type t = M0.t * M1.t

  let open_var i a (t0, t1) =
    M0.open_var i a t0, M1.open_var i a t1

  let close_var a i (t0, t1) =
    M0.close_var a i t0, M1.close_var a i t1
end


module Const (M : sig type t end) : S with type t = M.t =
struct
  type t = M.t
  let open_var _ _ x = x
  let close_var _ _ x = x
end

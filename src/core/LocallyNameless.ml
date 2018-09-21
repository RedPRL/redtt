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

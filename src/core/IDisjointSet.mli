(* Due to Conchon & Filliatre, heavily modified *)

module type S =
sig
  type t

  val init : size:int -> t
  val union : I.t -> I.t -> t -> t
  val hide : Name.t -> t -> t
  val test : I.t -> I.t -> t -> bool
end

module Make (T : RedBasis.PersistentTable.S) : S

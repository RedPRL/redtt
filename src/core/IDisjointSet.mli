(* Due to Conchon & Filliatre, heavily modified *)

module type S =
sig
  type t

  val init : size:int -> t
  val union : I.t -> I.t -> t -> t
  val subst : I.t -> Name.t -> t -> t
  val hide : Name.t -> t -> t
  val swap : Name.t -> Name.t -> t -> t
  val compare : I.t -> I.t -> t -> I.compare
end

module Make (T : RedBasis.PersistentTable.S) : S

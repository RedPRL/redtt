(* Due to Conchon & Filliatre *)

module type S =
sig
  type ('k, 'a) t

  val init : size:int -> ('k, 'a) t
  val get : 'k -> ('k, 'a) t -> 'a
  val set : 'k -> 'a -> ('k, 'a) t -> ('k, 'a) t

  val find : 'k -> ('k, 'a) t -> 'a option
end

module M : S

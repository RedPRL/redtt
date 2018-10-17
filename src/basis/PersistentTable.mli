(* Due to Conchon & Filliatre *)

module type S =
sig
  type ('k, 'a) t

  val init : size:int -> ('k, 'a) t
  val get : 'k -> ('k, 'a) t -> 'a
  val set : 'k -> 'a -> ('k, 'a) t -> ('k, 'a) t
  val mem : 'k -> ('k, 'a) t -> bool
  val remove : 'k -> ('k, 'a) t -> ('k, 'a) t
  val set_opt : 'k -> 'a option -> ('k, 'a) t -> ('k, 'a) t
  val find : 'k -> ('k, 'a) t -> 'a option
  val fold : ('k -> 'a -> 'b -> 'b) -> ('k, 'a) t -> 'b -> 'b
  val merge : ('k, 'a) t -> ('k, 'a) t -> ('k, 'a) t
end

module M : S

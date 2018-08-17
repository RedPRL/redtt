module Env :
sig
  type t
  val emp : t
  val var : int -> t -> string
  val bind : t -> string option -> string * t
  val bindn : t -> string option list -> string list * t
  val bind_fresh : t -> string * t

  val proj : t -> t
end

type env = Env.t

type 'a t0 = Format.formatter -> 'a -> unit
type 'a t = env -> 'a t0

val pp_list : 'a t0 -> 'a list t0

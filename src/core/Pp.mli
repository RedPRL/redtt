module Env :
sig
  type t
  val emp : t
  val var : int -> t -> string
  val bind : string option -> t -> string * t
  val bindn : string option list -> t -> string list * t
  val bind_fresh : t -> string * t

  val proj : t -> t
end

type env = Env.t

type 'a t0 = Format.formatter -> 'a -> unit
type 'a t = env -> 'a t0

val print_list : 'a t0 -> 'a list t0

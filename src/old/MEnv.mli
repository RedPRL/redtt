module type S =
sig
  val find : Symbol.t -> Tm.chk Tm.t option
end

type t

val make : (module S) -> t

val empty : t
val find : Symbol.t -> t -> Tm.chk Tm.t option

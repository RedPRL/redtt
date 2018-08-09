open RedBasis.Bwd

type 'a abs

type atom = Name.t

val pp : 'a Pp.t0 -> 'a abs Pp.t0

module type S =
sig
  type el

  include Sort.S with type 'a m = 'a with type t = el abs

  val bind : atom bwd -> el -> t
  val unleash : t -> atom bwd * el
  val inst : t -> I.t bwd -> el

  val len : t -> int

  val bind1 : atom -> el -> t
  val unleash1 : t -> atom * el
  val inst1 : t -> I.t -> el

  val make1 : (atom -> el) -> t
end

module M (X : Sort.S with type 'a m = 'a) : S with type el = X.t


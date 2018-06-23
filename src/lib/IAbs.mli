type 'a abs

type atom = Name.t

module type S =
sig
  type el

  include Sort.S with type 'a m = 'a with type t = el abs

  val bind : atom list -> el -> t
  val unleash : t -> atom list * el
  val inst : t -> I.t list -> el

  val bind1 : atom -> el -> t
  val unleash1 : t -> atom * el
  val inst1 : t -> I.t -> el

  val make1 : (atom -> el) -> t
end

module M (X : Sort.S with type 'a m = 'a) : S with type el = X.t


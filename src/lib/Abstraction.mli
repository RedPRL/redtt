type 'a abs

type atom = Symbol.t

module type S =
sig
  type el

  include Sort.S with type 'a m = 'a with type t = el abs

  val bind : atom -> el -> t
  val const : el -> t
  val unleash : t -> atom * el
  val inst : t -> Dim.t -> el
end

module M (X : Sort.S with type 'a m = 'a) : S with type el = X.t

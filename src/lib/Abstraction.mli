type 'a abs

type atom = Symbol.t

module M (X : Sort.S with type 'a m = 'a) :
sig
  include Sort.S with type 'a m = 'a with type t = X.t abs
  val bind : atom -> X.t -> t
  val unleash : t -> atom * X.t
  val inst : t -> Dim.t -> X.t
end

include module type of ValSig

module Error :
sig
  type t
  val pp : t Pp.t0
  exception E of t
end


module M (Sig : Sig) : S with module Sig = Sig

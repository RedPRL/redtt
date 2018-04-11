module type S = 
sig
  type t
  val emp : t

  exception Inconsistent
  val restrict_exn : t -> DimVal.t -> DimVal.t -> t
  val compare_dim : t -> DimVal.t -> DimVal.t -> DimVal.compare
end

include S
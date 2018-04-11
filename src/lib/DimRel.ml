module type S = 
sig
  type t
  val emp : t

  exception Inconsistent
  val restrict_exn : t -> DimVal.t -> DimVal.t -> t
  val compare_dim : t -> DimVal.t -> DimVal.t -> DimVal.compare
end

type t

let emp = failwith ""

exception Inconsistent

let restrict_exn _ _ _ = failwith "todo"

let compare_dim _ _ _ = failwith ""
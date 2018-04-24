module type S =
sig
  type t
  val emp : t

  exception Inconsistent
  val restrict_exn : t -> DimVal.t -> DimVal.t -> t
  val compare_dim : t -> DimVal.t -> DimVal.t -> DimVal.compare

  val canonize : t -> DimVal.t -> DimVal.t
end

module Vertex :
sig
  include Map.OrderedType with type t = DimVal.t
end =
struct
  type t = DimVal.t
  let compare = compare
end

exception Inconsistent


module Rel :
sig
  type t

  val emp : t
  val ext : t -> DimVal.t -> DimVal.t -> t
  val check : t -> DimVal.t -> DimVal.t -> bool
  val get : t -> DimVal.t -> DimVal.t
end =
struct
  module M = Map.Make (Vertex)

  type t = DimVal.t M.t

  let emp = M.empty

  let get g v =
    match M.find_opt v g with
    | Some v' -> min v v'
    | None -> v

  let can_link g d0 d1 =
    let d0' = get g d0 in
    let d1' = get g d1 in
    match DimVal.compare d0' d1' with
    | Apart -> false
    | _ -> true

  let ext g d0 d1 =
    let d0' = get g d0 in
    let d1' = get g d1 in
    let d = min d0' d1' in
    if can_link g d0' d1' then
      M.add d0' d @@ M.add d1' d @@ M.add d0 d @@ M.add d1 d g
    else
      raise Inconsistent

  let check g d0 d1 =
    match DimVal.compare (get g d0) (get g d1) with
    | Same -> true
    | _ -> false
end

type t = Rel.t

let emp = Rel.emp

let restrict_exn rel x y =
  Rel.ext rel x y

let compare_dim rel x y =
  DimVal.compare (Rel.get rel x) (Rel.get rel y)

let canonize rel x =
  Rel.get rel x
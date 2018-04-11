module type S =
sig
  type t
  val emp : t

  exception Inconsistent
  val restrict_exn : t -> DimVal.t -> DimVal.t -> t
  val compare_dim : t -> DimVal.t -> DimVal.t -> DimVal.compare
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
end =
struct
  module M = Map.Make (Vertex)
  module S = Set.Make (Vertex)

  type t = S.t M.t

  let emp = M.empty

  let get g v =
    match M.find_opt v g with
    | Some s -> g, s
    | None ->
      let s = S.empty in
      let g' = M.add v s g in
      g', s

  let can_link g d d' =
    let s = try M.find d g with _ -> S.empty in
    let s' = try M.find d' g with _ -> S.empty in
    let d_is_0 = S.mem DimVal.Dim0 s in
    let d_is_1 = S.mem DimVal.Dim1 s in
    let d'_is_0 = S.mem DimVal.Dim0 s' in
    let d'_is_1 = S.mem DimVal.Dim1 s' in
    not ((d_is_0 && d'_is_1) || (d_is_1 && d'_is_0))

  let ext g d0 d1 =
    if can_link g d0 d1 then
      M.update d1 (function Some s -> Some (S.add d0 s) | None -> Some (S.singleton d0)) @@
      M.update d0 (function Some s -> Some (S.add d1 s) | None -> Some (S.singleton d1)) g
    else
      raise Inconsistent

  let check g d0 d1 =
    match M.find_opt d0 g with
    | None -> false
    | Some s -> S.mem d1 s
end

let emp = Rel.emp

let restrict_exn rel x y =
  Rel.ext rel x y

let compare_dim rel x y =
  match DimVal.compare x y with
  | DimVal.Indeterminate ->
    if Rel.check rel x y then 
      DimVal.Same
    else
      DimVal.Indeterminate
  | r -> r
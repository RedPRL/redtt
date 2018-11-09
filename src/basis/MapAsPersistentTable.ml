module type S =
sig
  type key
  type 'a t

  val init : size:int -> 'a t
  val size : 'a t -> int
  val get : key -> 'a t -> 'a
  val set : key -> 'a -> 'a t -> 'a t
  val mem : key -> 'a t -> bool
  val remove : key -> 'a t -> 'a t
  val set_opt : key -> 'a option -> 'a t -> 'a t
  val find : key -> 'a t -> 'a option
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val merge : 'a t -> 'a t -> 'a t
  val to_list : 'a t -> (key * 'a) list
  val to_list_keys : 'a t -> key list
  val to_list_values : 'a t -> 'a list
end

module M (Ord : Map.OrderedType) : S with type key = Ord.t =
struct
  module M = Map.Make (Ord)

  type key = Ord.t
  type 'a t = 'a M.t

  let init ~size:_ = M.empty

  let size = M.cardinal

  let get = M.find

  let mem = M.mem

  let find = M.find_opt

  let set = M.add

  let remove = M.remove

  let set_opt k ov t =
    match ov with
    | None -> remove k t
    | Some v -> set k v t

  let fold = M.fold

  let merge t0 t1 = M.union (fun _ a _ -> Some a) t0 t1

  let to_list t = List.of_seq (M.to_seq t)

  let to_list_keys t = List.of_seq @@ Seq.map (fun (k, _) -> k) @@ M.to_seq t

  let to_list_values t = List.of_seq @@ Seq.map (fun (_, v) -> v) @@ M.to_seq t
end

module type S =
sig
  type ('k, 'a) t

  val init : size:int -> ('k, 'a) t
  val get : 'k -> ('k, 'a) t -> 'a
  val set : 'k -> 'a -> ('k, 'a) t -> ('k, 'a) t
end

module M : S =
struct
  type ('k, 'a) t = ('k, 'a) node ref
  and ('k, 'a) node =
    | Tbl of ('k, 'a) Hashtbl.t
    | Diff of 'k * 'a * ('k, 'a) t
    | Invalid

  exception Fatal

  let init ~size =
    ref @@ Tbl (Hashtbl.create size)

  let rec reroot t =
    match !t with
    | Tbl _ ->
      ()
    | Diff (k, v, t') ->
      reroot t';
      begin
        match !t' with
        | Tbl a as t'' ->
          Hashtbl.replace a k v;
          t := t'';
          t' := Invalid
        | _ ->
          raise Fatal
      end
    | Invalid ->
      raise Fatal

  let rec get k t =
    match !t with
    | Tbl a ->
      Hashtbl.find a k
    | Diff _ ->
      reroot t;
      begin
        match !t with
        | Tbl a ->
          Hashtbl.find a k
        | _ ->
          raise Fatal
      end
    | Invalid ->
      raise Fatal

  let set k v t =
    reroot t;
    match !t with
    | Tbl a as n ->
      let old = Hashtbl.find a k in
      Hashtbl.replace a k v;
      let res = ref n in
      t := Diff (k, old, res);
      res
    | _ ->
      raise Fatal

end

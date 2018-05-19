module type S =
sig
  type ('k, 'a) t

  val init : size:int -> ('k, 'a) t
  val get : 'k -> ('k, 'a) t -> 'a
  val set : 'k -> 'a -> ('k, 'a) t -> ('k, 'a) t

  val find : 'k -> ('k, 'a) t -> 'a option
end

module M : S =
struct
  type ('k, 'a) t = ('k, 'a) node ref
  and ('k, 'a) node =
    | Tbl of ('k, 'a) Hashtbl.t
    | Diff of 'k * 'a option * ('k, 'a) t

  exception Fatal

  let init ~size =
    ref @@ Tbl (Hashtbl.create size)

  let set_opt tbl k ov =
    match ov with
    | None -> Hashtbl.remove tbl k
    | Some v -> Hashtbl.replace tbl k v

  let rec reroot t =
    match !t with
    | Tbl _ ->
      ()
    | Diff (k, ov, t') ->
      reroot t';
      begin
        match !t' with
        | Tbl a as n ->
          let ov' = Hashtbl.find_opt a k in
          set_opt a k ov;
          t := n;
          t' := Diff (k, ov', t)
        | _ ->
          raise Fatal
      end

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

  let find k t =
    try
      Some (get k t)
    with
    | _ -> None

  let set k v t =
    reroot t;
    match !t with
    | Tbl a as n ->
      let old = Hashtbl.find_opt a k in
      Hashtbl.replace a k v;
      let res = ref n in
      t := Diff (k, old, res);
      res
    | _ ->
      raise Fatal

end

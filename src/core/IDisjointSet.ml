module type S =
sig
  type t

  val init : size:int -> t
  val union : I.t -> I.t -> t -> t
  val hide : Name.t -> t -> t
  val test : I.t -> I.t -> t -> bool
end

module Make (T : RedBasis.PersistentTable.S) : S =
struct
  type t =
    {index : (Name.t, int) T.t;
     next : int;
     rank : (int, int) T.t;
     mutable parent : (int, int I.f) T.t}

  let init ~size =
    {index = T.init ~size;
     next = 0;
     rank = T.init ~size;
     parent = T.init ~size}


  let rec find_aux (x : int) (f : (int, int I.f) T.t) : (int, int I.f) T.t * int I.f =
    try
      let fx = T.get x f in
      match T.get x f with
      | `Atom fx' as fx ->
        if fx' == x then
          f, fx
        else
          let f, cx = find_aux fx' f in
          let f = T.set x cx f in
          f, cx
      | fx -> f, fx
    with
    | _ ->
      let f = T.set x (`Atom x) f in
      f, `Atom x

  let find (x : int I.f) (h : t) : int I.f =
    match x with
    | `Atom x ->
      let f, cx = find_aux x h.parent in
      h.parent <- f;
      cx
    | c -> c

  let get_rank cx h =
    try
      T.get cx h.rank
    with
    | _ ->
      0

  let union_aux (x : int I.f) (y : int I.f) (h : t) =
    let cx = find x h in
    let cy = find y h in
    match cx, cy with
    | `Atom cx, `Atom cy ->
      if cx == cy then h else
      let rx = get_rank cx h in
      let ry = get_rank cy h in
      if rx > ry then
        {h with parent = T.set cy (`Atom cx) h.parent}
      else if rx < ry then
        {h with parent = T.set cx (`Atom cy) h.parent}
      else
        {h with
         rank = T.set cx (rx + 1) h.rank;
         parent = T.set cy (`Atom cx) h.parent}
    | `Atom cx, cy ->
      {h with parent = T.set cx cy h.parent}
    | cx, `Atom cy ->
      {h with parent = T.set cy cx h.parent}
    | cx, cy -> if cx == cy then h else raise I.Inconsistent

  let reserve_index (x : I.t) (h : t) : int I.f * t =
    match x with
    | `Atom x ->
      begin
        try `Atom (T.get x h.index), h
        with _ -> `Atom h.next, {h with index = T.set x h.next h.index; next = h.next + 1}
      end
    | `Dim0 -> `Dim0, h
    | `Dim1 -> `Dim1, h

  let union (x : I.t) (y : I.t) h =
    let x, h = reserve_index x h in
    let y, h = reserve_index y h in
    union_aux x y h

  let query_index x (index : (Name.t, int) T.t) : [`Ok of int I.f | `Owned] =
    match x with
    | `Atom x -> begin try `Ok (`Atom (T.get x index)) with _ -> `Owned end
    | `Dim0 -> `Ok `Dim0
    | `Dim1 -> `Ok `Dim1

  let test x y (h : t) =
    match query_index x h.index, query_index y h.index with
    | `Owned, `Owned -> x == y
    | `Owned, _ -> false
    | _, `Owned -> false
    | `Ok x, `Ok y -> find x h == find y h

  let hide (x : Name.t) (h : t) =
    {h with index = T.remove x h.index}

end

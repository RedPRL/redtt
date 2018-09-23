open RedBasis

type atom = I.atom
type dim = I.t
type cls = int I.f

module T = PersistentTable.M

type t =
  {index : (atom, int) T.t;
   next : int;
   rank : (int, int) T.t;
   mutable parent : (int, cls) T.t}

type 'a m = [`Changed of 'a | `Same]

let get_m h = function
  | `Changed h -> h
  | `Same -> h

let emp () =
  let size = 100 in
  {index = T.init ~size;
   next = 0;
   rank = T.init ~size;
   parent = T.init ~size}

let rec find_aux (x : int) (f : (int, cls) T.t) : (int, cls) T.t * cls =
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

let find' (x : int) (h : t) : cls =
  let f, cx = find_aux x h.parent in
  h.parent <- f;
  cx

let find (x : cls) (h : t) : cls =
  match x with
  | `Atom x -> find' x h
  | c -> c

let get_rank cx h =
  try
    T.get cx h.rank
  with
  | _ ->
    0

let union_aux (x : cls) (y : cls) (h : t) =
  let cx = find x h in
  let cy = find y h in
  match cx, cy with
  | `Atom cx, `Atom cy ->
    if cx == cy then `Same else
    let rx = get_rank cx h in
    let ry = get_rank cy h in
    if rx > ry then
      `Changed {h with parent = T.set cy (`Atom cx) h.parent}
    else if rx < ry then
      `Changed {h with parent = T.set cx (`Atom cy) h.parent}
    else
      `Changed
      {h with
       rank = T.set cx (rx + 1) h.rank;
       parent = T.set cy (`Atom cx) h.parent}
  | `Atom cx, cy ->
    `Changed {h with parent = T.set cx cy h.parent}
  | cx, `Atom cy ->
    `Changed {h with parent = T.set cy cx h.parent}
  | cx, cy ->
    if cx == cy then `Same else raise I.Inconsistent

let reserve_index_aux (x : atom) (h : t) : int * t =
  try
    T.get x h.index, h
  with
  | _ ->
    h.next, {h with index = T.set x h.next h.index; next = h.next + 1}

let reserve_index (x : dim) (h : t) : cls * t =
  match x with
  | `Atom x -> let x, h = reserve_index_aux x h in `Atom x, h
  | `Dim0 -> `Dim0, h
  | `Dim1 -> `Dim1, h

let union (x : dim) (y : dim) h =
  let x, h = reserve_index x h in
  let y, h = reserve_index y h in
  union_aux x y h

let query_index x (index : (atom, int) T.t) : [`Ok of cls | `Owned] =
  match x with
  | `Atom x ->
    begin
      try
        `Ok (`Atom (T.get x index))
      with
      _ ->
        `Owned
    end
  | `Dim0 -> `Ok `Dim0
  | `Dim1 -> `Ok `Dim1

let compare x y (h : t) =
  match query_index x h.index, query_index y h.index with
  | `Owned, `Owned ->
    if x == y then `Same else `Indet
  | `Owned, `Ok _ -> `Indet
  | `Ok _, `Owned -> `Indet
  | `Ok x, `Ok y ->
    match find x h, find y h with
    | `Atom x, `Atom y ->
      if x == y then `Same else `Indet
    | `Atom _, _ -> `Indet
    | _, `Atom _ -> `Indet
    | x, y -> if x = y then `Same else `Apart

let in_index (x : atom) (h : t) =
  T.mem x h.index

let hide_aux (x : atom) (h : t) =
  {h with index = T.remove x h.index}

let hide (x : atom) (h : t) =
  if in_index x h then
    `Changed (hide_aux x h)
  else
    `Same

let hide' (x : atom) (h : t) =
  get_m h (hide x h)

let equate = union

let equate' x y h =
  get_m h @@ equate x y h

let subst (r : dim) (x : atom) (h : t) =
  if in_index x h then
    hide x (equate' (`Atom x) r h)
  else
    `Same

let subst' r x h =
  get_m h @@ subst r x h

let swap (x : atom) (y : atom) (h : t) =
  if x == y then h else
  let x', h = reserve_index_aux x h in
  let y', h = reserve_index_aux y h in
  {h with index = T.set y x' (T.set x y' h.index)}


let pp_cls fmt =
  function
  | `Dim0 ->
    Format.fprintf fmt "0"
  | `Dim1 ->
    Format.fprintf fmt "1"
  | `Atom i ->
    Format.fprintf fmt "#%a" Format.pp_print_int i

let pp_parent fmt (x, cls) =
  Format.fprintf fmt "%a~%a" Name.pp x pp_cls cls

let pp fmt h =
  let comma fmt () = Format.fprintf fmt "," in
  let l = T.fold (fun x i l -> (x, find' i h) :: l) h.index [] in
  Format.pp_print_list ~pp_sep:comma pp_parent fmt l

(* poor man's tests *)
let _  =
  try
    let x = `Atom (Name.named (Some "i")) in
    let rst = equate' x `Dim1 @@ emp () in
    let rst = equate' x `Dim0 rst in
    failwith "Test failed"
  with
  | I.Inconsistent -> ()

let _ =
  let x = `Atom (Name.named (Some "i")) in
  let rst = equate' x `Dim0 @@ emp () in
  assert (compare x `Dim0 rst == `Same)

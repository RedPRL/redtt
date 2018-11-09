open RedBasis

type atom = I.atom
type dim = I.t
type cls = int I.f

module AtomT = MapAsPersistentTable.M (Name)
module IntT = MapAsPersistentTable.M (struct type t = int let compare = compare end)

type t =
  {index : int AtomT.t;
   next : int;
   rank : int IntT.t;
   parent : cls IntT.t}

let emp () =
  let size = 100 in
  {index = AtomT.init ~size;
   next = 0;
   rank = IntT.init ~size;
   parent = IntT.init ~size}

type 'a m = [`Changed of 'a | `Same | `Inconsistent]

let get_m h = function
  | `Changed h -> h
  | `Same -> h
  | `Inconsistent -> raise I.Inconsistent

(*
let find_index_with_compression (x : int) (h : t) : cls =
  let rec go x (parent : (int, cls) IntT.t) : cls * (int, cls) IntT.t =
    match IntT.get x parent with
    | `Atom x_parent as cur_cls ->
      let cls, parent = go x_parent parent in
      cls, if cur_cls = cls then parent else IntT.set x cls parent
    | cls -> cls, parent
    | exception Not_found ->
      `Atom x, parent
  in
  let cls, parent = go x h.parent in
  h.parent <- parent;
  cls
*)

(* the version without path compression *)
let rec find_index (x : int) (h : t) : cls =
  match IntT.get x h.parent with
  | `Atom x_parent -> find_index x_parent h
  | cls -> cls
  | exception Not_found -> `Atom x

let find_cls (x : cls) (h : t) : cls =
  match x with
  | `Atom x -> find_index x h
  | c -> c

let rank_index (x : int) h =
  try
    IntT.get x h.rank
  with
  | _ ->
    0

let union_cls (x : cls) (y : cls) (h : t) =
  let clsx = find_cls x h in
  let clsy = find_cls y h in
  match clsx, clsy with
  | `Dim0, `Dim0 | `Dim1, `Dim1 -> `Same
  | `Dim0, `Dim1 | `Dim1, `Dim0 -> `Inconsistent
  | `Atom clsx, `Atom clsy ->
    if clsx == clsy then `Same else
      let rx = rank_index clsx h in
      let ry = rank_index clsy h in
      if rx > ry then
        `Changed {h with parent = IntT.set clsy (`Atom clsx) h.parent}
      else if rx < ry then
        `Changed {h with parent = IntT.set clsx (`Atom clsy) h.parent}
      else
        `Changed
          {h with
           rank = IntT.set clsx (rx + 1) h.rank;
           parent = IntT.set clsy (`Atom clsx) h.parent}
  | `Atom clsx, clsy ->
    `Changed {h with parent = IntT.set clsx clsy h.parent}
  | clsx, `Atom clsy ->
    `Changed {h with parent = IntT.set clsy clsx h.parent}

let reserve_atom (x : atom) (h : t) : int * t =
  try
    AtomT.get x h.index, h
  with
  | _ ->
    h.next, {h with index = AtomT.set x h.next h.index; next = h.next + 1}

let reserve (x : dim) (h : t) : cls * t =
  match x with
  | `Atom x -> let x, h = reserve_atom x h in `Atom x, h
  | `Dim0 -> `Dim0, h
  | `Dim1 -> `Dim1, h

let union (x : dim) (y : dim) h =
  let x, h = reserve x h in
  let y, h = reserve y h in
  union_cls x y h

let query_atom (x : atom) (index : int AtomT.t) : [`Ok of cls | `Owned of atom] =
  try
    `Ok (`Atom (AtomT.get x index))
  with
    _ ->
    `Owned x

let query (x : dim) (index : int AtomT.t) : [`Ok of cls | `Owned of atom] =
  match x with
  | `Atom x -> query_atom x index
  | `Dim0 -> `Ok `Dim0
  | `Dim1 -> `Ok `Dim1

let compare x y (h : t) =
  match query x h.index, query y h.index with
  | `Owned x, `Owned y ->
    if x == y then `Same else `Indet
  | `Owned _, `Ok _ -> `Indet
  | `Ok _, `Owned _ -> `Indet
  | `Ok x, `Ok y ->
    match find_cls x h, find_cls y h with
    | `Dim0, `Dim0 | `Dim1, `Dim1 -> `Same
    | `Dim0, `Dim1 | `Dim1, `Dim0 -> `Apart
    | `Atom x, `Atom y ->
      if x == y then `Same else `Indet
    | `Atom _, _ -> `Indet
    | _, `Atom _ -> `Indet

let mem_atom (x : atom) index =
  AtomT.mem x index

let hide_aux (x : atom) (h : t) =
  {h with index = AtomT.remove x h.index}

let hide (x : atom) (h : t) =
  if mem_atom x h.index then
    `Changed (hide_aux x h)
  else
    `Same

let hide' (x : atom) (h : t) =
  if mem_atom x h.index then
    hide_aux x h
  else
    h

let equate = union

let equate' x y h =
  get_m h @@ equate x y h

let subst (r : dim) (x : atom) (h : t) =
  if mem_atom x h.index && r <> `Atom x then
    `Changed (hide_aux x (equate' (`Atom x) r h))
  else
    `Same

let subst' r x h =
  if mem_atom x h.index && r <> `Atom x then
    hide_aux x (equate' (`Atom x) r h)
  else
    h

let swap (x : atom) (y : atom) (h : t) =
  match AtomT.find x h.index, AtomT.find y h.index with
  | None, None -> h
  | Some idx, Some idy when idx = idy -> h
  | oidx, oidy -> {h with index = AtomT.set_opt y oidx (AtomT.set_opt x oidy h.index)}


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
  let l = AtomT.fold (fun x i l -> (x, find_index i h) :: l) h.index [] in
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





let from_old_restriction rst =
  let eqns = Restriction.chronicle rst in
  List.fold_left (fun rel (r, r') -> equate' r r' rel) (emp ()) eqns

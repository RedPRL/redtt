type atom = Symbol.t
type dim = Dim.t
module D = Dim

type delta =
  | Id
  | Equate of dim * dim
  | Cmp of delta * delta

module UF = DisjointSet.Make (PersistentTable.M)

type t =
  {classes : dim UF.t;
   chronicle : delta;
   size : int}

let rec eval_delta dl uf =
  match dl with
  | Id -> uf
  | Equate (r, r') ->
    UF.union r r' uf
  | Cmp (dl1, dl0) ->
    eval_delta dl1 @@ eval_delta dl0 uf

let emp =
  {classes = UF.init 100;
   chronicle = Id;
   size = 0}

let equate_ r r' t =
  let dl = Equate (r, r') in
  {chronicle = Cmp (dl, t.chronicle);
   classes = eval_delta dl t.classes;
   size = t.size + 1}

let equate r r' =
  equate_ r r' emp


let union_ t0 t1 =
  {chronicle = Cmp (t0.chronicle, t1.chronicle);
   classes = eval_delta t0.chronicle t1.classes;
   size = t0.size + t1.size}

exception Inconsistent

let canonize r t =
  try
    UF.find r t.classes
  with
  | _ -> r

let compare r r' t =
  let cr = canonize r t in
  let cr' = canonize r' t in
  D.compare cr cr'

let ensure_consistent t =
  match compare D.dim0 D.dim1 t with
  | D.Same ->
    raise Inconsistent
  | _ ->
    ()

let union t0 t1 =
  let res =
    if t0.size > t1.size then
      union_ t1 t0
    else
      union_ t0 t1
  in
  ensure_consistent res;
  res


let unleash r t =
  canonize r t

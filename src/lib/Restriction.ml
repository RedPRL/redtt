type atom = Symbol.t
type dim = DimVal.t
module D = DimVal
module P = Permutation

type delta =
  | Id
  | Equate of dim * dim
  | Cmp of delta * delta

module UF = DisjointSet.Make (PersistentTable.M)

type t =
  {classes : dim UF.t;
   chronicle : delta;
   perm : P.t;
   size : int}

let rec eval_delta pi dl uf =
  match dl with
  | Id -> uf
  | Equate (r, r') ->
    UF.union (P.read r pi) (P.read r' pi) uf
  | Cmp (dl1, dl0) ->
    eval_delta pi dl1 @@ eval_delta pi dl0 uf

let emp =
  {classes = UF.init 100;
   chronicle = Id;
   perm = P.emp;
   size = 0}

let equate_ r r' t =
  let dl = Equate (r, r') in
  {t with
   chronicle = Cmp (dl, t.chronicle);
   classes = eval_delta t.perm dl t.classes;
   size = t.size + 1}

let equate r r' =
  equate_ r r' emp


let union_ t0 t1 =
  {chronicle = Cmp (t0.chronicle, t1.chronicle);
   classes = eval_delta t0.perm t0.chronicle t1.classes;
   size = t0.size + t1.size;
   perm = t1.perm}

let union t0 t1 =
  if t0.size > t1.size then
    union_ t1 t0
  else
    union_ t0 t1

let perm pi t =
  {t with perm = P.cmp pi t.perm}

let canonize r t =
  P.read (UF.find (P.read r t.perm) t.classes) t.perm

let compare r r' t =
  let cr = UF.find (P.read r t.perm) t.classes in
  let cr' = UF.find (P.read r' t.perm) t.classes in
  D.compare cr cr'


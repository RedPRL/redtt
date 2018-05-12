type atom = Symbol.t
type dim = Dim.repr
module D = Dim

type eqn = dim * dim

module UF = DisjointSet.Make (PersistentTable.M)

type t =
  {classes : dim UF.t;
   chronicle : eqn list;
   size : int}

let rec eval_chronicle dl uf =
  match dl with
  | [] -> uf
  | (r, r') :: dl ->
    UF.union r r' @@ eval_chronicle dl uf

let pp_repr fmt r =
  match r with
  | D.Dim0 ->
    Format.fprintf fmt "0"
  | D.Dim1 ->
    Format.fprintf fmt "1"
  | D.Atom x ->
    Format.fprintf fmt "%s" @@ Symbol.to_string x

let pp_eqn fmt (r, r') =
  Format.fprintf fmt "%a=%a" pp_repr r pp_repr r'

let pp_chronicle fmt chr =
  let comma fmt () = Format.fprintf fmt ", " in
  Format.pp_print_list ~pp_sep:comma pp_eqn fmt chr


let emp =
  {classes = UF.init 100;
   chronicle = [];
   size = 0}

let equate_ r r' t =
  let dl = [r, r'] in
  {chronicle = dl @ t.chronicle;
   classes = eval_chronicle dl t.classes;
   size = t.size + 1}

exception Inconsistent

let find r t =
  try
    UF.find r t.classes
  with
  | _ -> r

let canonize r t =
  let rr = find r t in
  if rr = find D.Dim0 t then
    D.Dim0
  else if rr = find D.Dim1 t then
    D.Dim1
  else
    rr

let compare r r' t =
  let cr = canonize r t in
  let cr' = canonize r' t in
  D.compare_repr cr cr'


let equate r0 r1 t =
  let res = equate_ r0 r1 t in
  begin
    match compare D.Dim0 D.Dim1 res with
    | D.Same ->
      raise Inconsistent
    | _ -> ()
  end;
  res


let test =
  try
    let x = D.Atom (Symbol.named (Some "i")) in
    let rst = equate x D.Dim0 @@ equate x D.Dim1 emp in
    Format.printf "Test failure: {@[<1>%a@]}@.\n" pp_chronicle rst.chronicle;
    failwith "Test failed"
  with
  | Inconsistent -> ()


let unleash r t =
  canonize r t

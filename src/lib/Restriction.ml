open RedBasis

type atom = Name.t
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

let pp_eqn fmt (r, r') =
  Format.fprintf fmt "%a=%a" Dim.pp_repr r Dim.pp_repr r'

let pp_chronicle fmt chr =
  let comma fmt () = Format.fprintf fmt ", " in
  Format.pp_print_list ~pp_sep:comma pp_eqn fmt chr

let pp fmt rst =
  pp_chronicle fmt rst.chronicle


let emp =
  {classes = UF.init 100;
   chronicle = [];
   size = 0}

let equate_ r r' t =
  let dl = [r, r'] in
  {chronicle = dl @ t.chronicle;
   classes = UF.union r r' t.classes;
   size = t.size + 1}

exception Inconsistent

let find r t =
  try
    UF.find r t.classes
  with
  | _ -> r

let canonize r t =
  let rr = find r t in
  let res =
    if rr = find D.Dim0 t then
      D.Dim0
    else if rr = find D.Dim1 t then
      D.Dim1
    else
      rr
  in
  (* Format.printf "%a |= 0 ==> %a@." pp t D.pp_repr (find D.Dim0 t);
     Format.printf "Canonizing %a in %a as %a@." D.pp_repr r pp t D.pp_repr res; *)
  res

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
    let x = D.Atom (Name.named (Some "i")) in
    let rst = equate x D.Dim0 @@ equate x D.Dim1 emp in
    Format.printf "Test failure: {@[<1>%a@]}@.\n" pp_chronicle rst.chronicle;
    failwith "Test failed"
  with
  | Inconsistent -> ()

let test2 =
  let x = D.Atom (Name.named (Some "i")) in
  let rst = equate x D.Dim0 emp in
  assert (canonize x rst = D.Dim0)


let unleash r t =
  let r' = canonize r t in
  let rs = UF.find_class r' t.classes in
  Dim.from_reprs r' rs


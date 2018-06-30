open RedBasis

type atom = I.atom
type dim = I.t

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
  Format.fprintf fmt "%a=%a" I.pp r I.pp r'

let pp_chronicle fmt chr =
  let comma fmt () = Format.fprintf fmt ", " in
  Format.pp_print_list ~pp_sep:comma pp_eqn fmt chr

let pp fmt rst =
  pp_chronicle fmt rst.chronicle


let emp () =
  {classes = UF.init 100;
   chronicle = [];
   size = 0}

let equate_ r r' t =
  let dl = [r, r'] in
  {chronicle = dl @ t.chronicle;
   classes = UF.union r r' t.classes;
   size = t.size + 1}

exception Inconsistent = I.Inconsistent

let find r t =
  try
    UF.find r t.classes
  with
  | _ -> r

let canonize r t =
  let rr = find r t in
  let res =
    if rr = find `Dim0 t then
      `Dim0
    else if rr = find `Dim1 t then
      `Dim1
    else
      rr
  in
  (* Format.printf "%a |= 0 ==> %a@." pp t D.pp_repr (find D.Dim0 t);
     Format.printf "Canonizing %a in %a as %a@." D.pp_repr r pp t D.pp_repr res; *)
  res

let compare r r' t =
  let cr = canonize r t in
  let cr' = canonize r' t in
  I.compare cr cr'


let equate r0 r1 t =
  let res = equate_ r0 r1 t in
  begin
    match compare `Dim0 `Dim1 res with
    | `Same ->
      raise Inconsistent
    | _ -> ()
  end;
  res, I.equate r0 r1

let as_action t =
  let rec go =
    function
    | [] -> I.idn
    | (r, r') :: chr ->
      I.cmp (I.equate r r') (go chr)
  in
  go t.chronicle


let test =
  try
    let x = `Atom (Name.named (Some "i")) in
    let rst, _ = equate x `Dim1 @@ emp () in
    let rst, _ = equate x `Dim0 rst in
    Format.printf "Test failure: {@[<1>%a@]}@.\n" pp_chronicle rst.chronicle;
    failwith "Test failed"
  with
  | Inconsistent -> ()

let test2 =
  let x = `Atom (Name.named (Some "i")) in
  let rst, _ = equate x `Dim0 @@ emp () in
  assert (canonize x rst = `Dim0)



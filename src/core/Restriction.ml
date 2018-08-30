open RedBasis

type atom = I.atom
type dim = I.t

type eqn = dim * dim

module IDS = IDisjointSet.Make (PersistentTable.M)

type t =
  {classes : IDS.t;
   chronicle : eqn list;
   size : int}

let pp_eqn fmt (r, r') =
  Format.fprintf fmt "%a=%a" I.pp r I.pp r'

let pp_chronicle fmt chr =
  let comma fmt () = Format.fprintf fmt ", " in
  Format.pp_print_list ~pp_sep:comma pp_eqn fmt chr

let pp fmt rst =
  pp_chronicle fmt rst.chronicle


let emp () =
  {classes = IDS.init ~size:100;
   chronicle = [];
   size = 0}

let equate r r' t =
  let dl = [r, r'] in
  {chronicle = dl @ t.chronicle;
   classes = IDS.union r r' t.classes;
   size = t.size + 1}

let compare r r' t = IDS.test r r' t.classes

let as_action t =
  let rec go =
    function
    | [] -> I.idn
    | (r, r') :: chr ->
      I.cmp (I.equate r r') (go chr)
  in
  go t.chronicle

(* poor man's tests *)
let _  =
  try
    let x = `Atom (Name.named (Some "i")) in
    let rst = equate x `Dim1 @@ emp () in
    let rst = equate x `Dim0 rst in
    Format.printf "Test failure: {@[<1>%a@]}@.\n" pp_chronicle rst.chronicle;
    failwith "Test failed"
  with
  | I.Inconsistent -> ()

let _ =
  let x = `Atom (Name.named (Some "i")) in
  let rst = equate x `Dim0 @@ emp () in
  assert (compare x `Dim0 rst)

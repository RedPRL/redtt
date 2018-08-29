open RedBasis

type atom = I.atom
type dim = I.t

type eqn = dim * dim

module T = PersistentTable.M
module UF = DisjointSet.Make (T)

type t =
  {table : (dim, Name.t) T.t;
   untable : (Name.t, dim) T.t;
   classes : Name.t UF.t;
   chronicle : eqn list}
(* TODO: delete chronicle whenever possible *)

let name_dim0 = Name.fresh ()
let name_dim1 = Name.fresh ()

let pp_eqn fmt (r, r') =
  Format.fprintf fmt "%a=%a" I.pp r I.pp r'

let pp_chronicle fmt chr =
  let comma fmt () = Format.fprintf fmt ", " in
  Format.pp_print_list ~pp_sep:comma pp_eqn fmt chr

let pp fmt rst =
  pp_chronicle fmt rst.chronicle


let emp () =
  {table = T.set `Dim0 name_dim0 @@ T.set `Dim1 name_dim1 @@ T.init ~size:100;
   untable = T.set name_dim0 `Dim0 @@ T.set name_dim1 `Dim1 @@ T.init ~size:100;
   classes = UF.init ~size:100;
   chronicle = []}

let lookup_name r tbl untbl =
  match T.find r tbl with
  | Some x -> x, tbl, untbl
  | None ->
    let x = Name.fresh () in
    x, T.set r x tbl, T.set x r untbl

let equate_ r r' t =
  let dl = [r, r'] in
  let x, table, untable = lookup_name r t.table t.untable in
  let x', table, untable = lookup_name r' table untable in
  {chronicle = dl @ t.chronicle;
   table;
   untable;
   classes = UF.union x x' t.classes}

exception Inconsistent = I.Inconsistent

let find r t =
  try
    UF.find r t.classes
  with
  | _ -> r

let canonize r t =
  let repr, _, _ = lookup_name r t.table t.untable in
  let rr = find repr t in
  if rr = find name_dim0 t then
    `Dim0
  else if rr = find name_dim1 t then
    `Dim1
  else
    match T.find rr t.untable with
    | None -> r
    | Some r -> r

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

(* poor man's tests *)
let _  =
  try
    let x = `Atom (Name.named (Some "i")) in
    let rst, _ = equate x `Dim1 @@ emp () in
    let rst, _ = equate x `Dim0 rst in
    Format.printf "Test failure: {@[<1>%a@]}@.\n" pp_chronicle rst.chronicle;
    failwith "Test failed"
  with
  | Inconsistent -> ()

let _ =
  let x = `Atom (Name.named (Some "i")) in
  let rst, _ = equate x `Dim0 @@ emp () in
  assert (canonize x rst = `Dim0)



let rec act phi t =
  match phi with
  | I.Idn -> t
  | I.Swap (a, b) ->
    let x_b, _, _ = lookup_name (`Atom a) t.table t.untable in
    let x_a, _, _ = lookup_name (`Atom b) t.table t.untable in
    let table = T.set (`Atom b) x_b @@ T.set (`Atom a) x_a t.table in
    let untable = T.set x_b (`Atom b) @@ T.set x_a (`Atom a) t.untable in
    {t with
     table;
     untable;
     chronicle = List.map (fun (r, r') -> I.act phi r, I.act phi r') t.chronicle
    }
  | Cmp (phi0, phi1) ->
    let t = act phi1 t in
    act phi0 t
  | Subst (r, x) ->
    let t, _ = equate r (`Atom x) t in
    let x_x, _, _ = lookup_name (`Atom x) t.table t.untable in
    {t with
     table = T.delete r t.table;
     untable = T.delete x_x t.untable}

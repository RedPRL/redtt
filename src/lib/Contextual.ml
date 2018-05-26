open Dev
open RedBasis

type cx_l = entry list
type cx_r = entry list

type cx = cx_l * cx_r

module M =
struct
  type 'a m = params -> cx -> cx * 'a

  let ret a _ cx = cx, a

  let bind m k ps cx =
    let cx', a = m ps cx  in
    k a ps cx'
end

module Notation = Monad.Notation (M)
include M

open Notation

let local f m ps =
  m (f ps)

let ask ps cx = cx, ps

let get _ cx = cx, cx

let modify f _ cx = f cx, ()

let getl = fst <@> get
let getr = snd <@> get
let modifyl f = modify @@ fun (l, r) -> f l, r
let modifyr f = modify @@ fun (l, r) -> l, f r
let setl l = modifyl @@ fun _ -> l
let setr r = modifyr @@ fun _ -> r
let pushl e = modifyl @@ fun es -> e :: es
let pushr e = modifyr @@ fun es -> e :: es

let rec pushls es =
  match es with
  | [] -> ret ()
  | e :: es ->
    pushl e >>
    pushls es

let popl =
  getl >>= function
  | e :: mcx -> setl mcx >> ret e
  | _ -> failwith "popl: empty"

let popr =
  getr >>= function
  | e :: mcx -> setr mcx >> ret e
  | _ -> failwith "popr: empty"


let go_left =
  popl >>= pushr


let in_scope x p =
  local @@ fun ps ->
  (x, p) :: ps


let lookup_var x w =
  let rec go gm =
    match w, gm with
    | `Only, (y, P ty) :: gm ->
      if x = y then M.ret ty else go gm
    | `TwinL, (y, Tw (ty0, _)) :: gm ->
      if x = y then M.ret ty0 else go gm
    | `TwinR, (y, Tw (_, ty1)) :: gm ->
      if x = y then M.ret ty1 else go gm
    | _, _ :: gm ->
      go gm
    | _ ->
      failwith "lookup_var: not found"
  in
  ask >>= go

let lookup_meta x =
  let rec look =
    function
    | E (y, ty, _) :: mcx ->
      if x = y then M.ret ty else look mcx
    | _ :: mcx ->
      look mcx
    | [] ->
      failwith "lookup_meta: not found"
  in
  getl >>= look


let postpone s p =
  ask >>= fun ps ->
  let wrapped = List.fold_right (fun (x, e) p -> All (e, Dev.bind x p)) ps p in
  pushr @@ Q (s, wrapped)


let active = postpone Active
let block = postpone Blocked

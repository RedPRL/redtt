open Dev
open RedBasis
open Bwd open BwdNotation

type cx_l = entry bwd
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
let pushl e = modifyl @@ fun es -> es #< e
let pushr e = modifyr @@ fun es -> e :: es

let rec pushls es =
  match es with
  | [] -> ret ()
  | e :: es ->
    pushl e >>
    pushls es

let popl =
  getl >>= function
  | Snoc (mcx, e) -> setl mcx >> ret e
  | _ -> failwith "popl: empty"

let popr =
  getr >>= function
  | e :: mcx -> setr mcx >> ret e
  | _ -> failwith "popr: empty"


let go_left =
  popl >>= pushr


let in_scope x p =
  local @@ fun ps ->
  ps #< (x, p)


let lookup_var x w =
  let rec go gm =
    match w, gm with
    | `Only, Snoc (gm, (y, P ty)) ->
      if x = y then M.ret ty else go gm
    | `TwinL, Snoc (gm, (y, Tw (ty0, _))) ->
      if x = y then M.ret ty0 else go gm
    | `TwinR, Snoc (gm, (y, Tw (_, ty1))) ->
      if x = y then M.ret ty1 else go gm
    | _, Snoc (gm, _) ->
      go gm
    | _ ->
      failwith "lookup_var: not found"
  in
  ask >>= go

let lookup_meta x =
  let rec look =
    function
    | Snoc (mcx, E (y, ty, _)) ->
      if x = y then M.ret ty else look mcx
    | Snoc (mcx, _) ->
      look mcx
    | Emp ->
      failwith "lookup_meta: not found"
  in
  getl >>= look


let postpone s p =
  ask >>= fun ps ->
  let wrapped =
    let rec go ps p =
      match ps with
      | Snoc (ps, (x, e)) ->
        go ps @@ All (e, Dev.bind x p)
      | Emp -> p
    in go ps p
  in
  pushr @@ Q (s, wrapped)


let active = postpone Active
let block = postpone Blocked

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

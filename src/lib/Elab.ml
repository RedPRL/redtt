type mcx = MCx.t
type lcx = LCx.t
type rnv = ResEnv.t
type menv = MEnv.t
type hole = Symbol.t

module E = ElabMonad
module Notation = Monad.Notation (E)
open E.Notation
open Notation

module Tac = 
struct
  let lambda nm : unit E.m = 
    E.goal >>= fun ty ->
    match Tm.out ty with
    | Tm.Pi (dom, Tm.B (_, cod)) -> 
      E.oblige ([nm, dom] >- cod) >>= fun alpha ->
      E.fill @@ Tm.lam nm @@ Tm.up @@ Tm.meta alpha @@ Tm.inst0 @@ Tm.var 0

    | _ ->
      failwith "lambda: expected pi"

  let cons : unit E.m = 
    E.goal >>= fun ty ->
    match Tm.out ty with
    | Tm.Sg (dom, Tm.B (nm, cod)) ->
      E.oblige ([] >- dom) >>= fun alpha ->
      let tm0 = Tm.meta alpha Tm.Id in
      let cod' = Tm.let_ nm tm0 cod in
      E.oblige ([] >- cod') >>= fun beta ->
      let tm1 = Tm.meta beta Tm.Id in
      E.fill @@ Tm.cons (Tm.up tm0) (Tm.up tm1)

    | _ ->
      failwith "cons: expected sg"

  let pi nm : unit E.m = 
    E.goal >>= fun ty ->
    match Tm.out ty with
    | Tm.Univ lvl ->
      E.oblige ([] >- Tm.univ lvl) >>= fun alpha ->
      let dom = Tm.up @@ Tm.meta alpha Tm.Id in
      E.oblige ([nm, dom] >- Tm.univ lvl) >>= fun beta ->
      let cod = Tm.up @@ Tm.meta beta @@ Tm.inst0 @@ Tm.var 0 in
      E.fill @@ Tm.pi nm dom cod

    | _ ->
      failwith "pi: expected universe"

  let sg nm : unit E.m = 
    E.goal >>= fun ty ->
    match Tm.out ty with
    | Tm.Univ lvl ->
      E.oblige ([] >- Tm.univ lvl) >>= fun alpha ->
      let dom = Tm.up @@ Tm.meta alpha Tm.Id in
      E.oblige ([nm, dom] >- Tm.univ lvl) >>= fun beta ->
      let cod = Tm.up @@ Tm.meta beta @@ Tm.inst0 @@ Tm.var 0 in
      E.fill @@ Tm.sg nm dom cod

    | _ ->
      failwith "sg: expected universe"

  let under tac = 
    E.move0 `Down >>
    E.move (`Star `Right) >>
    tac >> 
    E.move0 `Up 

end

let rec elab : type a. a ElabTm.t -> unit E.m =
  fun etm ->
    match ElabTm.out etm with
    | ElabTm.Pi tele -> 
      let rec go tele =
        match tele with
        | ElabTm.TEnd {cod} -> 
          elab cod

        | ElabTm.TCons {vars; dom; cod} -> 
          go_vars vars dom >>
          go cod 

      and go_vars vars dom = 
        match vars with
        | [] -> 
          E.ret ()

        | x::xs ->
          Tac.pi (Some x) >>
          Tac.under begin
            elab dom >>
            E.move0 `Left >>
            go_vars xs dom
          end

      in
      go tele

    | _ -> 
      failwith "TODO"
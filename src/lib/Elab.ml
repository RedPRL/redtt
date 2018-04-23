type mcx = MCx.t
type lcx = LCx.t
type rnv = ResEnv.t
type menv = MEnv.t
type hole = Symbol.t

module E = ElabMonad
module Notation = Monad.Notation (E)
open E.Notation
open Notation

module Tm =
struct
  include Tm

  let var i = Tm.into @@ Tm.Var i
  let inst0 t = Tm.Sub (Tm.Id, t)

  let meta hole sub = Tm.into @@ Tm.Meta (hole, sub)
  let up t = Tm.into @@ Tm.Up t
  let lam nm t = Tm.into @@ Tm.Lam (Tm.B (nm, t))
  let pi nm dom cod = Tm.into @@ Tm.Pi (dom, Tm.B (nm, cod))
  let sg nm dom cod = Tm.into @@ Tm.Sg (dom, Tm.B (nm, cod))
  let let_ nm t0 t1 = Tm.into @@ Tm.Let (t0, Tm.B (nm, t1))
  let cons t0 t1 = Tm.into @@ Tm.Cons (t0, t1)
  let univ lvl = Tm.into @@ Tm.Univ lvl
end

module Tac = 
struct
  let lambda nm : unit E.m = 
    E.goal >>= fun ty ->
    match Tm.out ty with
    | Tm.Pi (dom, Tm.B (_, cod)) -> 
      E.oblige ([nm, dom] >- cod) >>= fun alpha ->
      let tm = 
        let inf = Tm.meta alpha @@ Tm.inst0 @@ Tm.var 0 in
        Tm.lam nm @@ Tm.up inf
      in
      E.fill tm

    | _ ->
      failwith "lambda: expected pi"

  let pi nm : unit E.m = 
    E.goal >>= fun ty ->
    match Tm.out ty with
    | Tm.Univ lvl ->
      E.oblige ([] >- Tm.univ lvl) >>= fun alpha ->
      let dom = Tm.up @@ Tm.meta alpha Tm.Id in
      E.oblige ([nm, dom] >- Tm.univ lvl) >>= fun beta ->
      let cod = Tm.up @@ Tm.meta beta @@ Tm.inst0 @@ Tm.var 0 in
      let tm = Tm.pi nm dom cod in
      E.fill tm

    | _ ->
      failwith "pi: expected universe"

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
          E.move `Down >>
          E.move `Right >>
          elab dom >>
          E.move `Left >>
          go_vars xs dom >>
          E.move `Up

      in
      go tele

    | _ -> 
      failwith "TODO"
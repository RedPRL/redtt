type mcx = MCx.t
type lcx = LCx.t
type rnv = ResEnv.t
type menv = MEnv.t
type hole = Symbol.t

module E = ElabMonad
module Notation = Monad.Notation (E)
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
end

(* Some preliminary sketches of the elaborator tactics. *)

let lambda x : hole -> hole E.m =
  fun alpha ->
    E.lookup_goal alpha >>= fun (cx, rnv, ty) ->
    match Tm.out ty with
    | Tm.Pi (dom, Tm.B (nm, cod)) -> 
      E.eval (LCx.env cx) dom >>= fun vdom ->
      let cx' = LCx.ext cx vdom in
      E.new_goal ~lcx:cx' ~rnv:(ResEnv.bind x rnv) ~ty:cod >>= fun beta ->
      let tm = 
        let inf = Tm.meta beta @@ Tm.inst0 @@ Tm.var 0 in
        Tm.lam nm @@ Tm.up inf
      in
      E.fill alpha tm >>
      E.ret beta

    | _ -> 
      failwith "lambda"

let pi x : hole -> (hole * hole) E.m = 
  fun alpha ->
    E.lookup_goal alpha >>= fun (lcx, rnv, ty) ->
    E.new_goal ~lcx ~rnv ~ty >>= fun alpha0 ->
    let tdom = Tm.up @@ Tm.meta alpha0 Tm.Id in
    E.eval (LCx.env lcx) tdom >>= fun vdom ->
    let lcx' = LCx.ext lcx vdom in
    let rnv' = ResEnv.bind x rnv in
    E.new_goal ~lcx:lcx' ~rnv:rnv' ~ty >>= fun alpha1 ->
    let tm = 
      let tcod = Tm.up @@ Tm.meta alpha1 @@ Tm.inst0 @@ Tm.var 0 in
      Tm.pi (Some x) tdom tcod
    in
    E.fill alpha tm >>
    E.ret (alpha0, alpha1)

let sg x : hole -> (hole * hole) E.m = 
  fun alpha ->
    E.lookup_goal alpha >>= fun (lcx, rnv, ty) ->
    E.new_goal ~lcx ~rnv ~ty >>= fun alpha0 ->
    let tdom = Tm.up @@ Tm.meta alpha0 Tm.Id in
    E.eval (LCx.env lcx) tdom >>= fun vdom ->
    let lcx' = LCx.ext lcx vdom in
    let rnv' = ResEnv.bind x rnv in
    E.new_goal ~lcx:lcx' ~rnv:rnv' ~ty >>= fun alpha1 ->
    let tm = 
      let tcod = Tm.up @@ Tm.meta alpha1 @@ Tm.inst0 @@ Tm.var 0 in
      Tm.sg (Some x) tdom tcod
    in
    E.fill alpha tm >>
    E.ret (alpha0, alpha1)

let cons : hole -> (hole * hole) E.m = 
  fun alpha ->
    E.lookup_goal alpha >>= fun (lcx, rnv, ty) ->
    match Tm.out ty with
    | Tm.Sg (dom, Tm.B (nm, cod)) ->
      E.new_goal ~lcx ~rnv ~ty:dom >>= fun alpha0 ->
      let tcar = Tm.meta alpha0 Tm.Id in
      let cod' = Tm.let_ nm tcar cod in
      E.new_goal ~lcx ~rnv ~ty:cod' >>= fun alpha1 ->
      let tm = 
        let tcdr = Tm.up @@ Tm.meta alpha1 Tm.Id in
        Tm.cons (Tm.up tcar) tcdr
      in
      E.fill alpha tm >>
      E.ret (alpha0, alpha1)

    | _ ->
      failwith "cons"

let quote rtm alpha : unit E.m = 
  E.lookup_res alpha >>= fun rnv ->
  let tm = rtm rnv in
  E.fill alpha tm

let rec elab : type a. a ElabTm.t -> hole -> unit E.m =
  fun etm alpha ->
    match ElabTm.out etm with
    | ElabTm.Pi tele -> 
      let rec go tele alpha =
        match tele with
        | ElabTm.TEnd {cod} -> 
          elab cod alpha

        | ElabTm.TCons {vars; dom; cod} -> 
          go_vars vars dom alpha >>=
          go cod 

      and go_vars vars dom alpha = 
        match vars with
        | [] -> 
          E.ret alpha

        | x::xs ->
          pi x alpha >>= fun (alpha0, alpha1) ->
          elab dom alpha0 >>
          go_vars xs dom alpha1

      in
      go tele alpha

    | ElabTm.Sg tele -> 
      let rec go tele alpha =
        match tele with
        | ElabTm.TEnd {cod} -> 
          elab cod alpha

        | ElabTm.TCons {vars; dom; cod} -> 
          go_vars vars dom alpha >>=
          go cod 

      and go_vars vars dom alpha = 
        match vars with
        | [] -> 
          E.ret alpha

        | x::xs ->
          sg x alpha >>= fun (alpha0, alpha1) ->
          elab dom alpha0 >>
          go_vars xs dom alpha1

      in
      go tele alpha

    | ElabTm.Lam {vars; bdy} ->
      let rec go xs alpha = 
        match xs with
        | [] -> 
          elab bdy alpha

        | x::xs ->
          lambda x alpha >>= 
          go xs
      in
      go vars alpha

    | ElabTm.Quote rtm ->
      quote rtm alpha

    | ElabTm.Tuple {cells} -> 
      let rec go cells alpha = 
        match cells with
        | [cell] -> 
          elab cell alpha

        | cell::cells -> 
          cons alpha >>= fun (alpha0, alpha1) ->
          elab cell alpha0 >>
          go cells alpha1

        | [] -> 
          failwith "TODO: empty tuple"
      in
      go cells alpha

    | _ -> 
      failwith "TODO"
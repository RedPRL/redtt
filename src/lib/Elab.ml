type mcx = MCx.t
type lcx = LCx.t
type rnv = ResEnv.t
type menv = MEnv.t
type hole = Symbol.t

module E = ElabMonad
let (>>=) = E.(>>=)
let (>>) = E.(>>)

(* Some preliminary sketches of the elaborator tactics. *)

let lambda x : hole -> hole E.m =
  fun alpha ->
    E.lookup_goal alpha >>= fun (cx, rnv, ty) ->
    match Tm.out ty with
    | Tm.Pi (dom, Tm.B cod) -> 
      E.eval (LCx.env cx) dom >>= fun vdom ->
      let cx' = LCx.ext cx vdom in
      let goal = MCx.{lcx = cx'; rnv = ResEnv.bind x rnv; ty = cod; cell = Ask} in
      E.new_goal goal >>= fun beta ->
      let tm = 
        let inf = Tm.into @@ Tm.Meta (beta, Tm.Sub (Tm.Id, Tm.into @@ Tm.Var 0)) in
        let chk = Tm.into @@ Tm.Up inf in
        Tm.into @@ Tm.Lam (Tm.B chk)
      in
      E.fill alpha tm >>
      E.ret beta

    | _ -> 
      failwith "lambda"

let pi x : hole -> (hole * hole) E.m = 
  fun alpha ->
    E.lookup_goal alpha >>= fun (lcx, rnv, ty) ->
    let gdom = MCx.{lcx; rnv; ty; cell = Ask} in
    E.new_goal gdom >>= fun alpha0 ->
    let tdom = Tm.into @@ Tm.Meta (alpha0, Tm.Id) in
    E.eval (LCx.env lcx) tdom >>= fun vdom ->
    let lcx' = LCx.ext lcx vdom in
    let rnv' = ResEnv.bind x rnv in
    let gcod = MCx.{lcx = lcx'; rnv = rnv'; ty; cell = Ask} in
    E.new_goal gcod >>= fun alpha1 ->
    let tm = 
      let tcod = Tm.into @@ Tm.Up (Tm.into @@ Tm.Meta (alpha1, Tm.Sub (Tm.Id, Tm.into @@ Tm.Var 0))) in
      Tm.into @@ Tm.Pi (Tm.into @@ Tm.Up tdom, Tm.B tcod)
    in
    E.fill alpha tm >>
    E.ret (alpha0, alpha1)

let sg x : hole -> (hole * hole) E.m = 
  fun alpha ->
    E.lookup_goal alpha >>= fun (lcx, rnv, ty) ->
    let gdom = MCx.{lcx; rnv; ty; cell = Ask} in
    E.new_goal gdom >>= fun alpha0 ->
    let tdom = Tm.into @@ Tm.Meta (alpha0, Tm.Id) in
    E.eval (LCx.env lcx) tdom >>= fun vdom ->
    let lcx' = LCx.ext lcx vdom in
    let rnv' = ResEnv.bind x rnv in
    let gcod = MCx.{lcx = lcx'; rnv = rnv'; ty; cell = Ask} in
    E.new_goal gcod >>= fun alpha1 ->
    let tm = 
      let tcod = Tm.into @@ Tm.Up (Tm.into @@ Tm.Meta (alpha1, Tm.Sub (Tm.Id, Tm.into @@ Tm.Var 0))) in
      Tm.into @@ Tm.Sg (Tm.into @@ Tm.Up tdom, Tm.B tcod)
    in
    E.fill alpha tm >>
    E.ret (alpha0, alpha1)

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

    | _ -> 
      failwith "TODO"
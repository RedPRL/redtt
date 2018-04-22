type env = 
  {mcx : MCx.t}

type hole = Symbol.t

type 'a tactic = env -> env * 'a 

let (>>=) m k env = 
  let env', a = m env in
  k a env'

let (>>) m n =
  m >>= fun _ -> n

let ret x env = 
  env, x

let get env = env, env

(* Some preliminary sketches of the elaborator tactics. *)

let lambda ~name : hole -> hole tactic =
  fun alpha env ->
    let seq = MCx.lookup_exn alpha env.mcx in
    let menv = failwith "TODO" in
    match Val.out @@ Val.eval (menv, LCx.env seq.lcx) seq.ty with
    | Val.Pi (dom, cod) ->
      let beta = Symbol.fresh () in
      let goal = 
        let vdom = Val.eval_clo dom in
        let lcx = LCx.ext seq.lcx vdom in
        let vgen = Val.generic vdom @@ LCx.len seq.lcx in
        let vcod = Val.inst_bclo cod vgen in
        let univ = Val.into @@ Val.Univ Lvl.Omega in
        let tcod = Quote.quote_can ~n:(LCx.len seq.lcx + 1) ~ty:univ ~can:vcod in
        MCx.{lcx; rnv = ResEnv.bind name seq.rnv; ty = tcod; cell = Ask} in
      let mcx' = MCx.ext beta goal env.mcx in
      {mcx = mcx'}, beta

    | _ -> failwith "Foo"

let rec lambdas ~names:xs : hole -> hole tactic =
  fun alpha ->
    match xs with
    | [] -> 
      ret alpha

    | x::xs ->
      lambda ~name:x alpha >>= 
      lambdas ~names:xs

let fill tm : hole -> unit tactic =
  fun alpha env ->
    let seq = MCx.lookup_exn alpha env.mcx in
    let menv = failwith "" in
    let vty = Val.eval (menv, LCx.env seq.lcx) seq.ty in
    let tm = tm seq.rnv in
    Typing.check ~mcx:{mcx = env.mcx; menv} ~cx:seq.lcx ~ty:vty ~tm:tm;
    let env' = {mcx = MCx.set alpha tm env.mcx} in
    env', ()

let rec compile_chk : hole -> Tm.chk ElabTm.t -> unit tactic =
  fun alpha etm ->
    match ElabTm.out etm with
    | ElabTm.Lam {vars; bdy} ->
      lambdas ~names:vars alpha >>= fun beta ->
      compile_chk beta bdy

    | ElabTm.Quote tm -> 
      fill tm alpha

    | _ -> 
      failwith ""
type env = 
  {mcx : MCx.t}

type hole = Symbol.t

type 'a tactic = env -> env * 'a 

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
type mcx = MCx.t
type lcx = LCx.t
type rnv = ResEnv.t
type menv = MEnv.t
type hole = Symbol.t


type 'a m = mcx -> mcx * 'a 

let (>>=) m k cx = 
  let cx', a = m cx in
  k a cx'

let (>>) m n =
  m >>= fun _ -> n

let ret x cx = 
  cx, x

let get_env cx = 
  cx, cx

let get_menv cx =
  cx, MCx.menv cx

let lookup alpha cx =
  cx, MCx.lookup_exn alpha cx

let lookup_goal alpha = 
  get_menv >>= fun menv ->
  lookup alpha >>= fun seq ->
  let vty = Val.eval (menv, LCx.env seq.lcx) seq.ty in
  let univ = Val.into @@ Val.Univ Lvl.Omega in
  let nty = Quote.quote_can ~n:(LCx.len seq.lcx) ~ty:univ ~can:vty in
  ret (seq.lcx, seq.rnv, nty)

let lookup_res alpha = 
  lookup alpha >>= fun seq ->
  ret seq.rnv

let new_goal ~lcx ~rnv ~ty  : hole m =
  fun cx ->
    let alpha = Symbol.fresh () in
    let cx' = MCx.ext alpha MCx.{lcx; rnv; ty; cell = Ask} cx in
    cx', alpha

let fill alpha tm : unit m =
  fun cx ->
    let cx' = MCx.set alpha tm cx in
    cx', ()

let eval env tm =
  get_menv >>= fun menv ->
  ret @@ Val.eval (menv, env) tm

module V = Val
module Q = Quote
module T = Tm

module Cx :
sig
  type t
  val ext_ty : t -> V.value -> t * V.value
  val eval : t -> 'a T.t -> V.value
end =
struct
  type t = {env : V.env; qenv : Q.env}

  let ext_ty {env; qenv} vty =
    let n = Q.Env.len qenv in
    let var = V.into @@ V.Up {ty = vty; neu = V.Lvl n} in
    {env = V.Val var :: env;
     qenv = Q.Env.succ qenv},
    var

  let eval {env; _} tm =
    V.eval env tm
end

type cx = Cx.t

let rec check cx ty tm =
  match V.unleash ty, T.out tm with
  | V.Pi {dom; cod}, T.Lam (T.B (_, tm)) ->
    let cxx, x = Cx.ext_ty cx dom in
    let vcod = V.inst_clo cod x in
    check cxx vcod tm

  | V.Sg {dom; cod}, T.Cons (t0, t1) ->
    let v = check_eval cx dom t0 in
    let vcod = V.inst_clo cod v in
    check cx vcod t1

  | _ -> failwith ""

and check_eval cx ty tm =
  check cx ty tm;
  Cx.eval cx tm

and infer _ _ =
  failwith "TODO"

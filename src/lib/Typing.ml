module V = Val
module Q = Quote
module T = Tm

module Cx :
sig
  type t
  val ext_ty : t -> V.value -> t * V.value

  val eval : t -> 'a T.t -> V.value
  val eval_dim : t -> T.chk T.t -> V.dim

  val lookup : int -> t -> [`Ty of V.value | `Dim]
end =
struct
  type hyp = [`Ty of V.value | `Dim]

  type t = {tys : hyp list; env : V.env; qenv : Q.env}

  let ext_ty {env; qenv; tys} vty =
    let n = Q.Env.len qenv in
    let var = V.make @@ V.Up {ty = vty; neu = V.Lvl n} in
    {env = V.Val var :: env;
     tys = `Ty vty :: tys;
     qenv = Q.Env.succ qenv},
    var

  let eval {env; _} tm =
    V.eval env tm

  let eval_dim {env; _} tm =
    V.eval_dim env tm

  let lookup i {tys; _} =
    List.nth tys i
end

type cx = Cx.t

let infer_dim cx tr =
  match T.unleash tr with
  | T.Var ix ->
    begin
      match Cx.lookup ix cx with
      | `Dim -> ()
      | _ -> failwith "infer_dim: expected dimension"
    end
  | _ ->
    failwith "infer_dim: expected dimension"

let check_dim cx tr =
  match T.unleash tr with
  | T.Dim0 ->
    ()
  | T.Dim1 ->
    ()
  | T.Up tr ->
    infer_dim cx tr
  | _ ->
    failwith "check_dim: expected dimension"



let rec check cx ty tm =
  match V.unleash ty, T.unleash tm with
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

and check_eval_dim cx tr =
  check_dim cx tr;
  Cx.eval_dim cx tr

and infer cx tm =
  match Tm.unleash tm with
  | T.Var ix ->
    begin
      match Cx.lookup ix cx with
      | `Ty ty -> ty
      | `Dim -> failwith "infer: expected type hypothesis"
    end

  | T.Car tm ->
    let dom, _ = V.unleash_sg @@ infer cx tm in
    dom

  | T.Cdr tm ->
    let _, cod = V.unleash_sg @@ infer cx tm in
    let v = Cx.eval cx tm in
    V.inst_clo cod @@ V.car v

  | T.FunApp (tm0, tm1) ->
    let dom, cod = V.unleash_pi @@ infer cx tm0 in
    let v1 = check_eval cx dom tm1 in
    V.inst_clo cod v1

  | T.ExtApp (tm, tr) ->
    let r = check_eval_dim cx tr in
    let ext_ty = infer cx tm in
    let ty, _ = V.unleash_ext ext_ty r in
    ty

  | T.VProj info ->
    failwith "TODO: this doesn't yet have enough information: we need to change it to carry every part of the V type"

  | _ ->
    failwith "infer"


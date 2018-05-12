module V = Val
module Q = Quote
module T = Tm
module R = Restriction

module Cx :
sig
  type t
  val ext_ty : t -> V.value -> t * V.value
  val ext_dim : t -> t * V.atom
  val restrict : t -> Dim.t -> Dim.t -> t

  val eval : t -> 'a T.t -> V.value
  val eval_dim : t -> T.chk T.t -> V.dim


  val lookup : int -> t -> [`Ty of V.value | `Dim]
  val compare_dim : t -> Dim.t -> Dim.t -> Dim.compare
  val check_eq : t -> ty:V.value -> V.value -> V.value -> unit
  val check_subtype : t -> V.value -> V.value -> unit
end =
struct
  type hyp = [`Ty of V.value | `Dim]

  type t = {tys : hyp list; env : V.env; qenv : Q.env; rel : R.t}

  let ext_ty {env; qenv; tys; rel} vty =
    let n = Q.Env.len qenv in
    let var = V.make @@ V.Up {ty = vty; neu = V.Lvl n} in
    {env = V.Val var :: env;
     tys = `Ty vty :: tys;
     qenv = Q.Env.succ qenv;
     rel},
    var

  let ext_dim {env; qenv; tys; rel} =
    let x = Symbol.fresh () in
    {env = V.Atom x :: env;
     tys = `Dim :: tys;
     qenv = Q.Env.abs qenv x;
     rel}, x

  let eval {env; rel; _} tm =
    V.eval rel env tm

  let eval_dim {env; rel; _} tm =
    V.eval_dim rel env tm

  let lookup i {tys; _} =
    List.nth tys i

  let restrict cx r r' =
    {cx with rel = R.union (R.equate r r') cx.rel}

  let compare_dim cx r r' =
    R.compare r r' cx.rel

  let check_eq cx ~ty el0 el1 =
    Q.equiv cx.qenv ~ty el0 el1

  let check_subtype cx ty0 ty1 =
    Q.subtype cx.qenv ty0 ty1
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
  | V.Univ lvl0, T.Univ lvl1 ->
    if Lvl.greater lvl0 lvl1 then () else
      failwith "Predicativity violation"

  | V.Univ _, T.Pi (dom, B (_, cod)) ->
    let vdom = check_eval cx ty dom in
    let cxx', _ = Cx.ext_ty cx vdom in
    check cxx' ty cod

  | V.Univ _, T.Sg (dom, B (_, cod)) ->
    let vdom = check_eval cx ty dom in
    let cxx, _ = Cx.ext_ty cx vdom in
    check cxx ty cod

  | V.Univ _, T.Ext (B (_, (cod, sys))) ->
    let cxx, _ = Cx.ext_dim cx in
    let vcod = check_eval cxx ty cod in
    check_ext_sys cxx vcod sys

  | V.Univ _, T.V info ->
    check_dim cx info.r;
    let ty0 = check_eval cx ty info.ty0 in
    let ty1 = check_eval cx ty info.ty1 in
    check_is_equivalence cx ~ty0 ~ty1 ~equiv:info.equiv

  | V.Univ _, T.Bool ->
    ()

  | V.Pi {dom; cod}, T.Lam (T.B (_, tm)) ->
    let cxx, x = Cx.ext_ty cx dom in
    let vcod = V.inst_clo cod x in
    check cxx vcod tm

  | V.Sg {dom; cod}, T.Cons (t0, t1) ->
    let v = check_eval cx dom t0 in
    let vcod = V.inst_clo cod v in
    check cx vcod t1

  | V.Ext ext_abs, T.ExtLam (B (_, tm)) ->
    let cxx, x = Cx.ext_dim cx in
    let codx, sysx = V.ExtAbs.inst ext_abs (Dim.named x) in
    check_boundary cxx codx sysx tm

  | _, T.Up tm ->
    let ty' = infer cx tm in
    Cx.check_subtype cx ty' ty

  | _ -> failwith ""

and check_boundary cx ty sys tm =
  let rec go sys =
    match sys with
    | [] -> ()
    | face :: sys ->
      check_boundary_face cx ty face tm;
      go sys
  in
  check cx ty tm;
  go sys

and check_boundary_face cx ty face tm =
  match face with
  | Face.True (_, _, el) ->
    Cx.check_eq cx ~ty el @@
    Cx.eval cx tm

  | Face.False _ ->
    ()

  | Face.Indet (p, el) ->
    let r, r' = DimStar.unleash p in
    let cx' = Cx.restrict cx r r' in
    let phi = Dim.equate r r' in
    Cx.check_eq cx' ~ty:(V.Val.act phi ty) el @@
    Cx.eval cx' tm

and check_ext_sys cx ty sys =
  let rec go sys acc =
    match sys with
    | [] ->
      ()
    | (tr0, tr1, otm) :: sys ->
      let r0 = check_eval_dim cx tr0 in
      let r1 = check_eval_dim cx tr1 in
      begin
        match Cx.compare_dim cx r0 r1, otm with
        | Dim.Apart, None ->
          go sys acc

        | (Dim.Same | Dim.Indeterminate), Some tm ->
          let phi = Dim.equate r0 r0 in
          let cx' = Cx.restrict cx r0 r1 in
          check cx' (V.Val.act phi ty) tm;

          (* Check tube-tube adjacency conditions *)
          go_adj cx' acc (r0, r1, tm);
          go sys @@ (r0, r1, tm) :: acc

        | _ ->
          failwith "check_ext_sys"
      end

  and go_adj cx faces face =
    match faces with
    | [] -> ()
    | (r'0, r'1, tm') :: faces ->
      (* Invariant: cx should already be restricted by r0=r1 *)
      let r0, r1, tm = face in
      begin
        try
          let cx' = Cx.restrict cx r'0 r'1 in
          let v = Cx.eval cx' tm in
          let v' = Cx.eval cx' tm' in
          let phi = Dim.cmp (Dim.equate r'0 r'1) (Dim.equate r0 r1) in
          Cx.check_eq cx' ~ty:(V.Val.act phi ty) v v'
        with
        | R.Inconsistent -> ()
      end;
      go_adj cx faces face
  in
  go sys []

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
    let v_ty =
      check_eval_ty cx @@
      T.make @@ T.V {r = info.r; ty0 = info.ty0; ty1 = info.ty1; equiv = info.equiv}
    in
    check cx v_ty info.tm;
    Cx.eval cx info.ty1

  | T.Coe _info ->
    let _cxx, _x = Cx.ext_dim cx in
    (* check_ty cxx info.ty; *)
    failwith "TODO"

  | T.Com _info ->
    failwith "TODO"

  | T.HCom _info ->
    failwith "TODO"

  | T.FCom _info ->
    failwith "TODO"


  | T.Down info ->
    let ty = check_eval_ty cx info.ty in
    check cx ty info.tm;
    ty

  | _ ->
    failwith "infer"


and check_eval cx ty tm =
  check cx ty tm;
  Cx.eval cx tm

and check_ty cx ty =
  let univ = V.make @@ V.Univ Lvl.Omega in
  check cx univ ty

and check_eval_dim cx tr =
  check_dim cx tr;
  Cx.eval_dim cx tr

and check_eval_ty cx ty =
  check_ty cx ty;
  Cx.eval cx ty

and check_is_equivalence cx ~ty0 ~ty1 ~equiv =
  let type_of_equiv = V.Macro.equiv ty0 ty1 in
  check cx type_of_equiv equiv

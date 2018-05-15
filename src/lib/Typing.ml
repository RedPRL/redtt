module V = Val
module Q = Quote
module T = Tm
module R = Restriction

type value = V.value

module Cx :
sig
  type t
  val emp : t

  val ext_ty : t -> nm:string option -> value -> t * value
  val ext_el : t -> nm:string option -> ty:value -> el:value -> t
  val ext_dim : t -> nm:string option -> t * V.atom
  val ext_dims : t -> nms:string option list -> t * V.atom list
  val restrict : t -> Dim.repr -> Dim.repr -> t

  val eval : t -> 'a T.t -> V.value
  val eval_dim : t -> T.chk T.t -> Dim.repr

  val ppenv : t -> Pretty.env

  val lookup : int -> t -> [`Ty of V.value | `Dim]
  val compare_dim : t -> Dim.repr -> Dim.repr -> Dim.compare
  val check_eq : t -> ty:V.value -> V.value -> V.value -> unit
  val check_subtype : t -> V.value -> V.value -> unit

  val unleash_dim : t -> Dim.repr -> Dim.t
  val equate_dim : t -> Dim.repr -> Dim.repr -> Dim.action
end =
struct
  type hyp = [`Ty of V.value | `Dim]

  (* The way that we model dimensions is now incompatible with the union-find version of things.
     We need to find a new way. *)
  type t = {tys : hyp list; env : V.env; qenv : Q.env; rel : R.t; ppenv : Pretty.env}

  let emp =
    {env = [];
     qenv = Q.Env.emp;
     tys = [];
     ppenv = Pretty.Env.emp;
     rel = R.emp}

  let ext_ty {env; qenv; tys; rel; ppenv} ~nm vty =
    let n = Q.Env.len qenv in
    let var = V.make @@ V.Up {ty = vty; neu = V.Lvl (nm, n)} in
    {env = V.Val var :: env;
     tys = `Ty vty :: tys;
     qenv = Q.Env.succ qenv;
     ppenv = snd @@ Pretty.Env.bind nm ppenv;
     rel},
    var

  let ext_el {env; qenv; tys; rel; ppenv} ~nm ~ty ~el =
    {env = V.Val el :: env;
     tys = `Ty ty :: tys;
     qenv = Q.Env.succ qenv; (* Is this right? *)
     ppenv = snd @@ Pretty.Env.bind nm ppenv;
     rel}

  let ext_dim {env; qenv; tys; rel; ppenv} ~nm =
    let x = Symbol.named nm in
    {env = V.Atom x :: env;
     tys = `Dim :: tys;
     qenv = Q.Env.abs qenv [x];
     ppenv = snd @@ Pretty.Env.bind nm ppenv;
     rel}, x

  let ext_dims _ ~nms:_ =
    failwith "TODO: ext_dims"

  let ppenv cx =
    cx.ppenv

  let eval {env; rel; _} tm =
    V.eval rel env tm

  let eval_dim {env; rel; _} tm =
    V.eval_dim rel env tm

  let lookup i {tys; _} =
    List.nth tys i

  let restrict cx r r' =
    {cx with rel = R.equate r r' cx.rel}

  let equate_dim cx r r' =
    let cr = R.unleash r cx.rel in
    let cr' = R.unleash r' cx.rel in
    Dim.equate cr cr'

  let compare_dim cx r r' =
    R.compare r r' cx.rel

  let unleash_dim cx r =
    R.unleash r cx.rel

  let check_eq cx ~ty el0 el1 =
    try
      Q.equiv cx.qenv ~ty el0 el1
    with
    | exn ->
      Format.printf "check_eq: %a /= %a@." V.pp_value el0 V.pp_value el1;
      raise exn

  let check_subtype cx ty0 ty1 =
    try
      Q.subtype cx.qenv ty0 ty1
    with
    | exn ->
      Format.printf "subtype: %a /<= %a@." V.pp_value ty0 V.pp_value ty1;
      raise exn
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

  | V.Univ _, T.Pi (dom, B (nm, cod)) ->
    let vdom = check_eval cx ty dom in
    let cxx', _ = Cx.ext_ty cx ~nm vdom in
    check cxx' ty cod

  | V.Univ _, T.Sg (dom, B (nm, cod)) ->
    let vdom = check_eval cx ty dom in
    let cxx, _ = Cx.ext_ty cx ~nm vdom in
    check cxx ty cod

  | V.Univ _, T.Ext (NB (nms, (cod, sys))) ->
    let cxx, _ = Cx.ext_dims cx ~nms in
    let vcod = check_eval cxx ty cod in
    check_ext_sys cxx vcod sys

  | V.Univ _, T.V info ->
    check_dim cx info.r;
    let ty0 = check_eval cx ty info.ty0 in
    let ty1 = check_eval cx ty info.ty1 in
    check_is_equivalence cx ~ty0 ~ty1 ~equiv:info.equiv

  | V.Univ _, T.Bool ->
    ()

  | V.Pi {dom; cod}, T.Lam (T.B (nm, tm)) ->
    let cxx, x = Cx.ext_ty cx ~nm dom in
    let vcod = V.inst_clo cod x in
    check cxx vcod tm

  | V.Sg {dom; cod}, T.Cons (t0, t1) ->
    let v = check_eval cx dom t0 in
    let vcod = V.inst_clo cod v in
    check cx vcod t1

  | V.Ext ext_abs, T.ExtLam (T.NB (nms, tm)) ->
    let cxx, xs = Cx.ext_dims cx ~nms in
    let codx, sysx = V.ExtAbs.inst ext_abs @@ List.map Dim.named xs in
    check_boundary cxx codx sysx tm

  | V.Univ _, T.FCom info ->
    check_fcom cx ty info.r info.r' info.cap info.sys

  | V.Bool, (T.Tt | T.Ff) ->
    ()

  | _, T.Up tm ->
    let ty' = infer cx tm in
    Cx.check_subtype cx ty' ty

  | _, T.Let (t0, T.B (nm, t1)) ->
    let ty' = infer cx t0 in
    let el = Cx.eval cx t0 in
    let cx' = Cx.ext_el cx ~nm ~ty:ty' ~el in
    check cx' ty t1

  | _ ->
    Format.eprintf "Failed to check term %a@." (Tm.pp (Cx.ppenv cx)) tm;
    failwith "Type error"

and check_fcom cx ty tr tr' tcap tsys =
  let r = check_eval_dim cx tr in
  check_dim cx tr';
  let cxx, x = Cx.ext_dim cx ~nm:None in
  let cap = check_eval cx ty tcap in
  check_comp_sys cx r (cxx, x, ty) cap tsys

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
    let cx' = Cx.restrict cx (Dim.unleash r) (Dim.unleash r') in
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
          begin
            try
              let phi = Cx.equate_dim cx r0 r1 in
              let cx' = Cx.restrict cx r0 r1 in
              check cx' (V.Val.act phi ty) tm;

              (* Check tube-tube adjacency conditions *)
              go_adj cx' acc (r0, r1, tm);
            with R.Inconsistent -> ()
          end;
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
          let phi = Dim.cmp (Cx.equate_dim cx r'0 r'1) (Cx.equate_dim cx r0 r1) in
          Cx.check_eq cx' ~ty:(V.Val.act phi ty) v v'
        with
        | R.Inconsistent -> ()
      end;
      go_adj cx faces face
  in
  go sys []

and check_comp_sys cx r (cxx, x, tyx) cap sys =
  let rec go sys acc =
    match sys with
    | [] ->
      ()
    | (tr0, tr1, obnd) :: sys ->
      let r0 = check_eval_dim cx tr0 in
      let r1 = check_eval_dim cx tr1 in
      begin
        match Cx.compare_dim cx r0 r1, obnd with
        | Dim.Apart, None ->
          go sys acc

        | (Dim.Same | Dim.Indeterminate), Some bnd ->
          begin
            try
              (* check that bnd is a section of tyx under r0=r1 *)
              let cxxr0r1 = Cx.restrict cxx r0 r1 in
              let phir0r1 = Dim.equate (Dim.singleton r0) (Dim.singleton r1) in
              let T.B (_, tm) = bnd in
              check cxxr0r1 (V.Val.act phir0r1 tyx) tm;

              (* check that tm<r/x> = cap under r0=r1 *)
              let cxr0r1 = Cx.restrict cx r0 r1 in
              let phirx = Dim.subst (Dim.singleton r) x in
              Cx.check_eq cxr0r1 ~ty:(V.Val.act phirx tyx) (V.Val.act phir0r1 cap) (V.Val.act phirx cap);
              (* Check tube-tube adjacency conditions *)
              go_adj cxxr0r1 acc (r0, r1, bnd);
            with
              R.Inconsistent -> ()
          end;

          go sys @@ (r0, r1, bnd) :: acc

        | _ ->
          failwith "check_ext_sys"
      end

  and go_adj cxx faces face =
    match faces with
    | [] -> ()
    | (r'0, r'1, bnd') :: faces ->
      let T.B (_, tm') = bnd' in
      (* Invariant: cx should already be restricted by r0=r1 *)
      let r0, r1, bnd = face in
      let T.B (_, tm) = bnd in
      begin
        try
          let cxx' = Cx.restrict cxx r'0 r'1 in
          let v = Cx.eval cxx' tm in
          let v' = Cx.eval cxx' tm' in
          let phi = Dim.cmp (Dim.equate (Dim.singleton r'0) (Dim.singleton r'1)) (Dim.equate (Dim.singleton r0) (Dim.singleton r1)) in
          Cx.check_eq cxx' ~ty:(V.Val.act phi tyx) v v'
        with
        | R.Inconsistent -> ()
      end;
      go_adj cx faces face

  in go sys []

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
    let rs = List.map (check_eval_dim cx) tr in
    let ext_ty = infer cx tm in
    let ty, _ = V.unleash_ext ext_ty @@ List.map (Cx.unleash_dim cx) rs in
    ty

  | T.VProj info ->
    let v_ty =
      check_eval_ty cx @@
      T.make @@ T.V {r = info.r; ty0 = info.ty0; ty1 = info.ty1; equiv = info.equiv}
    in
    check cx v_ty info.tm;
    Cx.eval cx info.ty1

  | T.Coe info ->
    let r = check_eval_dim cx info.r in
    let r' = check_eval_dim cx info.r' in
    let T.B (nm, ty) = info.ty in
    let cxx, x = Cx.ext_dim cx ~nm in
    let vtyx = check_eval_ty cxx ty in
    let vtyr = V.Val.act (Dim.subst (Cx.unleash_dim cx r) x) vtyx in
    check cx vtyr info.tm;
    V.Val.act (Dim.subst (Cx.unleash_dim cx r') x) vtyx

  | T.Com info ->
    let r = check_eval_dim cx info.r in
    let r' = check_eval_dim cx info.r' in
    let T.B (nm, ty) = info.ty in
    let cxx, x = Cx.ext_dim cx ~nm in
    let vtyx = check_eval_ty cxx ty in
    let vtyr = V.Val.act (Dim.subst (Dim.singleton r) x) vtyx in
    let cap = check_eval cx vtyr info.cap in
    check_comp_sys cx r (cxx, x, vtyx) cap info.sys;
    V.Val.act (Dim.subst (Dim.singleton r') x) vtyx

  | T.HCom info ->
    let r = check_eval_dim cx info.r in
    check_dim cx info.r';
    let cxx, x = Cx.ext_dim cx ~nm:None in
    let vty = check_eval_ty cx info.ty in
    let cap = check_eval cx vty info.cap in
    check_comp_sys cx r (cxx, x, vty) cap info.sys;
    vty

  | T.If info ->
    let T.B (nm, mot) = info.mot in
    let bool = V.make V.Bool in
    let cxx, _= Cx.ext_ty cx ~nm bool in
    check_ty cxx mot;

    let scrut_ty = infer cx info.scrut in
    Cx.check_eq cx ~ty:(V.make @@ V.Univ Lvl.Omega) scrut_ty bool;
    let scrut = Cx.eval cx info.scrut in

    let cx_tt = Cx.ext_el cx ~nm ~ty:bool ~el:(V.make V.Tt) in
    let cx_ff = Cx.ext_el cx ~nm ~ty:bool ~el:(V.make V.Ff) in
    let mot_tt = Cx.eval cx_tt mot in
    let mot_ff = Cx.eval cx_ff mot in
    check cx mot_tt info.tcase;
    check cx mot_ff info.fcase;

    let cx_scrut = Cx.ext_el cx ~nm ~ty:bool ~el:scrut in
    Cx.eval cx_scrut mot


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

and check_eval_dim cx tr : Dim.repr =
  check_dim cx tr;
  Cx.eval_dim cx tr

and check_eval_ty cx ty =
  check_ty cx ty;
  Cx.eval cx ty

and check_is_equivalence cx ~ty0 ~ty1 ~equiv =
  let type_of_equiv = V.Macro.equiv ty0 ty1 in
  check cx type_of_equiv equiv

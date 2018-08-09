module Q = Quote
module T = Tm
module D = Domain

type value = D.value

type cx = Cx.t

open RedBasis
open Bwd
open BwdNotation

type cofibration = (I.t * I.t) list

type error =
  | ExpectedDimension of cx * Tm.tm
  | ExpectedTick of cx * Tm.tm

exception E of error

module Error =
struct
  type t = error
  exception E = E

  let pp fmt =
    function
    | ExpectedDimension (cx, tm) ->
      Format.fprintf fmt
        "Expected dimension, but got %a."
        (Tm.pp (Cx.ppenv cx)) tm
    | ExpectedTick (cx, tm) ->
      Format.fprintf fmt
        "Expected tick, but got %a."
        (Tm.pp (Cx.ppenv cx)) tm

end

let rec check_dim cx tr =
  match T.unleash tr with
  | T.Dim0 ->
    ()
  | T.Dim1 ->
    ()
  | T.Up cmd ->
    check_dim_cmd cx cmd
  | _ ->
    raise @@ E (ExpectedDimension (cx, tr))

and check_dim_cmd cx =
  function
  | hd, Emp ->
    begin
      match hd with
      | Tm.Ix (ix, _) ->
        begin
          match Cx.lookup ix cx with
          | `I -> ()
          | _ -> failwith "check_dim_cmd: expected dimension"
        end
      | Tm.Var _ ->
        (* TODO: lookup in global context, make sure it is a dimension *)
        ()
      | _ -> failwith ""
    end
  | _ ->
    failwith "check_dim_cmd"

let rec check_tick cx tr =
  match T.unleash tr with
  | T.TickConst ->
    ()
  | T.Up cmd ->
    check_tick_cmd cx cmd
  | _ ->
    raise @@ E (ExpectedTick (cx, tr))

and check_tick_cmd cx =
  function
  | hd, Emp ->
    begin
      match hd with
      | Tm.Ix (ix, _) ->
        begin
          match Cx.lookup ix cx with
          | `Tick -> ()
          | _ -> failwith "check_tick_cmd: expected dimension"
        end
      | Tm.Var _ ->
        (* TODO: lookup in global context, make sure it is a dimension *)
        ()
      | _ ->
        failwith ""
    end
  | _ ->
    failwith "check_dim_cmd"

let check_dim_scope oxs r =
  match oxs with
  | None -> ()
  | Some xs ->
    match r with
    | `Atom x ->
      if List.exists (fun y -> x = y) xs then () else failwith "Bad dimension scope"
    | _ -> ()

let check_valid_cofibration ?xs:(xs = None) cofib =
  let zeros = Hashtbl.create 20 in
  let ones = Hashtbl.create 20 in
  let rec go eqns =
    match eqns with
    | [] -> false
    | (r, r') :: eqns ->
      check_dim_scope xs r;
      check_dim_scope xs r';
      begin
        match I.compare r r' with
        | `Same -> true
        | `Apart -> go eqns
        | `Indet ->
          match r, r' with
          | `Dim0, `Dim1 -> go eqns
          | `Dim1, `Dim0 -> go eqns
          | `Dim0, `Dim0 -> true
          | `Dim1, `Dim1 -> true
          | `Atom x, `Dim0 ->
            if Hashtbl.mem ones x then true else
              begin
                Hashtbl.add zeros x ();
                go eqns
              end
          | `Atom x, `Dim1 ->
            if Hashtbl.mem zeros x then true else
              begin
                Hashtbl.add ones x ();
                go eqns
              end
          | `Atom x, `Atom y ->
            x = y || go eqns
          | _, _ ->
            go @@ (r', r) :: eqns
      end
  in
  if go cofib then () else failwith "check_valid_cofibration"

let check_extension_cofibration xs cofib =
  match cofib with
  | [] -> ()
  | _ ->
    check_valid_cofibration ~xs:(Some xs) cofib

let rec check cx ty tm =
  let (module V) = Cx.evaluator cx in
  match V.unleash ty, T.unleash tm with
  | D.Univ info0, T.Univ info1 ->
    (* TODO: what about kinds? I think it's fine, since we learned from Andy Pitts how to make
       the pretype universe Kan. But I may need to add those "ecom" thingies, LOL. *)
    if Lvl.greater info0.lvl info1.lvl then () else
      failwith "Predicativity violation"

  | D.Univ _, T.Pi (dom, B (nm, cod)) ->
    let vdom = check_eval cx ty dom in
    let cxx', _ = Cx.ext_ty cx ~nm vdom in
    check cxx' ty cod

  | D.Univ _, T.Sg (dom, B (nm, cod)) ->
    let vdom = check_eval cx ty dom in
    let cxx, _ = Cx.ext_ty cx ~nm vdom in
    check cxx ty cod

  | D.Univ _, T.Later (B (nm, cod)) ->
    let cxx, _ = Cx.ext_tick cx ~nm in
    check cxx ty cod

  | D.Univ _, T.BoxModality t ->
    let cx' = Cx.ext_lock cx in
    check cx' ty t

  | D.Univ univ, T.Ext (NB (nms, (cod, sys))) ->
    let cxx, xs = Cx.ext_dims cx ~nms:(Bwd.to_list nms) in
    let vcod = check_eval cxx ty cod in
    if Kind.lte univ.kind Kind.Kan then
      check_extension_cofibration xs @@ cofibration_of_sys cxx sys
    else
      ();
    check_ext_sys cxx vcod sys

  | D.Univ univ, T.Rst info ->
    if univ.kind = Kind.Pre then () else failwith "Restriction type is not Kan";
    let ty = check_eval cx ty info.ty in
    check_ext_sys cx ty info.sys

  | D.Univ univ, T.CoR (tr, tr', oty) ->
    if univ.kind = Kind.Pre then () else failwith "Co-restriction type is not known to be Kan";
    let r = check_eval_dim cx tr in
    let r' = check_eval_dim cx tr' in
    begin
      match I.compare r r', oty with
      | `Apart, None ->
        ()
      | _, Some ty' ->
        let cxrr', _ = Cx.restrict cx r r' in
        check cxrr' ty ty'
      | _ ->
        failwith "co-restriction type malformed"
    end

  | D.Univ _, T.V info ->
    check_dim cx info.r;
    let ty0 = check_eval cx ty info.ty0 in
    let ty1 = check_eval cx ty info.ty1 in
    check_is_equivalence cx ~ty0 ~ty1 ~equiv:info.equiv

  | D.Univ _, T.Data dlbl ->
    let _ = GlobalEnv.lookup_datatype dlbl @@ Cx.globals cx in
    ()

  | D.Data dlbl, T.Intro (dlbl', clbl, args) when dlbl = dlbl' ->
    let desc = GlobalEnv.lookup_datatype dlbl @@ Cx.globals cx in
    let constr = Desc.lookup_constr clbl desc in
    check_constr cx dlbl constr args


  | D.Pi {dom; cod}, T.Lam (T.B (nm, tm)) ->
    let cxx, x = Cx.ext_ty cx ~nm dom in
    let vcod = V.inst_clo cod x in
    check cxx vcod tm

  | D.Later tclo, T.Next (T.B (nm, tm)) ->
    let cxx, tck = Cx.ext_tick cx ~nm in
    let vty = V.inst_tick_clo tclo tck in
    check cxx vty tm

  | D.BoxModality vty, T.Shut tm ->
    let cx' = Cx.ext_lock cx in
    check cx' vty tm

  | D.Sg {dom; cod}, T.Cons (t0, t1) ->
    let v = check_eval cx dom t0 in
    let vcod = V.inst_clo cod v in
    check cx vcod t1

  | D.Ext ext_abs, T.ExtLam (T.NB (nms, tm)) ->
    let cxx, xs = Cx.ext_dims cx ~nms:(Bwd.to_list nms) in
    let codx, sysx = Domain.ExtAbs.inst ext_abs @@ Bwd.map (fun x -> `Atom x) @@ Bwd.from_list xs in
    check_boundary cxx codx sysx tm

  | D.CoR ty_face, T.CoRThunk (tr0, tr1, otm) ->
    let r'0 = check_eval_dim cx tr0 in
    let r'1 = check_eval_dim cx tr1 in
    begin
      match ty_face, otm with
      | Face.False _, None ->
        ()
      | Face.True (r0, r1, ty), Some tm ->
        begin
          match I.compare r'0 r0, I.compare r'1 r1 with
          | `Same, `Same ->
            check cx ty tm
          | _ ->
            failwith "co-restriction mismatch"
        end
      | Face.Indet (p, ty), Some tm ->
        let r0, r1 = Eq.unleash p in
        begin
          match I.compare r'0 r0, I.compare r'1 r1 with
          | `Same, `Same ->
            begin
              try
                let cx', phi = Cx.restrict cx r'0 r'1 in
                check cx' (Domain.Value.act phi ty) tm
              with
              | I.Inconsistent -> ()
            end
          | _ ->
            failwith "co-restriction mismatch"
        end
      | _ ->
        Format.eprintf "@.@.type restriction didn't match thunk@.@.";
        failwith "Malformed element of co-restriction type"
    end

  | D.Rst {ty; sys}, _ ->
    check cx ty tm;
    check_boundary cx ty sys tm

  | D.Univ _, T.FHCom info ->
    check_fhcom cx ty info.r info.r' info.cap info.sys

  | D.Univ _, T.LblTy info ->
    check cx ty info.ty;
    let go_arg (ty, tm) =
      let vty = check_eval_ty cx ty in
      check cx vty tm
    in
    List.iter go_arg info.args

  | D.LblTy info, T.LblRet t ->
    check cx info.ty t

  | D.V vty, T.VIn vin ->
    let r = check_eval_dim cx vin.r in
    begin
      match I.compare (`Atom vty.x) r with
      | `Same ->
        let cx', phi = Cx.restrict cx (`Atom vty.x) `Dim0 in
        let el0 = check_eval cx' vty.ty0 vin.tm0 in
        let el1 = check_eval cx vty.ty1 vin.tm1 in
        Cx.check_eq cx' ~ty:(D.Value.act phi vty.ty1) (V.apply (V.car vty.equiv) el0) @@ D.Value.act phi el1
      | _ ->
        failwith "v/vin dimension mismatch"
    end

  | _, T.Up tm ->
    let ty' = infer cx tm in
    Cx.check_subtype cx ty' ty

  | _, T.Let (cmd, T.B (nm, t1)) ->
    let ty' = infer cx cmd in
    let el = Cx.eval_cmd cx cmd in
    let cx' = Cx.def cx ~nm ~ty:ty' ~el in
    check cx' ty t1

  | _ ->
    (* Format.eprintf "Failed to check term %a@." (Tm.pp (CxUtil.ppenv cx)) tm; *)
    failwith "Type error"

and check_constr cx dlbl constr tms =
  let vdataty = D.make @@ D.Data dlbl in
  let rec go cx' const_specs rec_specs dim_specs tms =
    match const_specs, rec_specs, dim_specs, tms with
    | [], rec_specs, dim_specs, _ ->
      let tms, trs = ListUtil.split (List.length rec_specs) tms in
      List.iter2 (fun (_, Desc.Self) tm -> check cx vdataty tm) rec_specs tms;
      List.iter2 (fun _ tm -> check_dim cx tm) dim_specs trs;
    | (plbl, ty) :: const_specs, rec_specs, dim_specs, tm :: tms ->
      let vty = Cx.eval cx' ty in
      let varg = check_eval cx vty tm in
      let cx' = Cx.def cx ~nm:(Some plbl) ~ty:vty ~el:varg in
      go cx' const_specs rec_specs dim_specs tms
    | _ -> failwith "constructor arguments malformed"
  in
  go cx constr.const_specs constr.rec_specs constr.dim_specs tms

and cofibration_of_sys : type a. cx -> (Tm.tm, a) Tm.system -> cofibration =
  fun cx sys ->
    let face (tr, tr', _) =
      let r = Cx.eval_dim cx tr in
      let r' = Cx.eval_dim cx tr' in
      (r, r')
    in
    List.map face sys

and check_fhcom cx ty tr tr' tcap tsys =
  let r = check_eval_dim cx tr in
  check_dim cx tr';
  let cxx, x = Cx.ext_dim cx ~nm:None in
  let cap = check_eval cx ty tcap in
  check_valid_cofibration @@ cofibration_of_sys cx tsys;
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
    let r, r' = Eq.unleash p in
    try
      let cx', phi = Cx.restrict cx r r' in
      Cx.check_eq cx' ~ty:(D.Value.act phi ty) el @@
      Cx.eval cx' tm
    with
    | I.Inconsistent ->
      ()



and check_ext_sys cx ty sys =
  let rec go sys acc =
    match sys with
    | [] ->
      ()
    | (tr0, tr1, otm) :: sys ->
      let r0 = check_eval_dim cx tr0 in
      let r1 = check_eval_dim cx tr1 in
      begin
        match I.compare r0 r1, otm with
        | `Apart, _ ->
          go sys acc

        | (`Same | `Indet), Some tm ->
          begin
            try
              let cx', phi = Cx.restrict cx r0 r1 in
              check cx' (D.Value.act phi ty) tm;

              (* Check face-face adjacency conditions *)
              go_adj cx' acc (r0, r1, tm)
            with
            | I.Inconsistent -> ()
          end;
          go sys @@ (r0, r1, tm) :: acc

        | _, None ->
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
          let cx', phi = Cx.restrict cx r'0 r'1 in
          let v = Cx.eval cx' tm in
          let v' = Cx.eval cx' tm' in
          let phi = I.cmp phi (I.equate r0 r1) in
          Cx.check_eq cx' ~ty:(D.Value.act phi ty) v v'
        with
        | I.Inconsistent -> ()
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
        match I.compare r0 r1, obnd with
        | `Apart, _ ->
          go sys acc

        | (`Same | `Indet), Some bnd ->
          begin
            try
              (* check that bnd is a section of tyx under r0=r1 *)
              let cxxr0r1, phir0r1= Cx.restrict cxx r0 r1 in
              let T.B (_, tm) = bnd in
              check cxxr0r1 (D.Value.act phir0r1 tyx) tm;

              (* check that tm<r/x> = cap under r0=r1 *)
              let cxr0r1, _ = Cx.restrict cx r0 r1 in
              let phirx = I.cmp phir0r1 @@ I.subst r x in
              Cx.check_eq cxr0r1
                ~ty:(D.Value.act phirx tyx)
                (D.Value.act phir0r1 cap)
                (D.Value.act phirx cap);

              (* Check face-face adjacency conditions *)
              go_adj cxxr0r1 acc (r0, r1, bnd)
            with
              I.Inconsistent -> ()
          end;

          go sys @@ (r0, r1, bnd) :: acc

        | _, None ->
          failwith "check_comp_sys"
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
          let cxx', phir'0r'1 = Cx.restrict cxx r'0 r'1 in
          let v = Cx.eval cxx' tm in
          let v' = Cx.eval cxx' tm' in
          let phi = I.cmp phir'0r'1 (I.equate r0 r1) in
          Cx.check_eq cxx' ~ty:(D.Value.act phi tyx) v v'
        with
        | I.Inconsistent -> ()
      end;
      go_adj cxx faces face

  in go sys []

and infer cx (hd, sp) =
  let D.{ty; _} = infer_spine cx hd sp in
  ty

and infer_spine cx hd =
  let (module V) = Cx.evaluator cx in
  function
  | Emp ->
    D.{el = Cx.eval_head cx hd; ty = infer_head cx hd}

  | Snoc (sp, frm) ->
    match frm with
    | T.Car ->
      let ih = infer_spine cx hd sp in
      let dom, _ = V.unleash_sg ih.ty in
      D.{el = V.car ih.el; ty = dom}

    | T.Cdr ->
      let ih = infer_spine cx hd sp in
      let _, cod = V.unleash_sg ih.ty in
      let car = V.car ih.el in
      D.{el = V.cdr ih.el; ty = V.inst_clo cod car}

    | T.FunApp t ->
      let ih = infer_spine cx hd sp in
      let dom, cod = V.unleash_pi ih.ty in
      let v = check_eval cx dom t in
      D.{el = V.apply ih.el v; ty = V.inst_clo cod v}

    | T.ExtApp ts ->
      let ih = infer_spine cx hd sp in
      let rs = List.map (check_eval_dim cx) ts in
      let ty, _ = V.unleash_ext_with ih.ty rs in
      D.{el = V.ext_apply ih.el rs; ty}

    | T.VProj info ->
      let ih = infer_spine cx hd sp in
      let v_ty =
        check_eval_ty cx @@
        T.make @@ T.V {r = info.r; ty0 = info.ty0; ty1 = info.ty1; equiv = info.equiv}
      in
      Cx.check_eq_ty cx v_ty ih.ty;
      D.{el = Cx.eval_frame cx ih.el frm; ty = Cx.eval cx info.ty1}

    | T.Elim info ->
      let T.B (nm, mot) = info.mot in
      let ih = infer_spine cx hd sp in
      let mot_clo =
        let cxx, _= Cx.ext_ty cx ~nm ih.ty in
        check_ty cxx mot;
        Cx.make_closure cx info.mot
      in

      let desc = V.Sig.lookup_datatype info.dlbl in
      let used_labels = Hashtbl.create 10 in


      let check_clause earlier_clauses lbl constr =
        let open Desc in
        if Hashtbl.mem used_labels lbl then failwith "Duplicate case in eliminator";
        Hashtbl.add used_labels lbl ();

        let _, Tm.NB (_, bdy) = List.find (fun (lbl', _) -> lbl = lbl') info.clauses in

        (* 'cx' is local context extended with hyps;
           'env' is the environment for evaluating the types that comprise
           the constructor, and should therefore begin with the *empty* environment. *)
        let rec build_cx cx env (nms, cvs, rvs, rs) const_specs rec_specs dim_specs =
          match const_specs, rec_specs, dim_specs with
          | (plbl, pty) :: const_specs, _, _ ->
            let vty = V.eval env pty in
            let cx', v = Cx.ext_ty cx ~nm:(Some plbl) vty in
            build_cx cx' (D.Env.push (`Val v) env) (nms #< (Some plbl), cvs #< v, rvs, rs) const_specs rec_specs dim_specs
          | [], (nm, Self) :: rec_specs, _ ->
            let cx_x, v_x = Cx.ext_ty cx ~nm:(Some nm) ih.ty in
            let cx_ih, _ = Cx.ext_ty cx_x ~nm:None @@ V.inst_clo mot_clo v_x in
            build_cx cx_ih env (nms #< (Some nm) #< None, cvs, rvs #< v_x, rs) const_specs rec_specs dim_specs
          | [], [], nm :: dim_specs ->
            let cx', x = Cx.ext_dim cx ~nm:(Some nm) in
            build_cx cx' env (nms #< (Some nm), cvs, rvs, rs #< (`Atom x)) const_specs rec_specs dim_specs
          | [], [], [] ->
            cx, nms, Bwd.to_list cvs, Bwd.to_list rvs, Bwd.to_list rs
        in
        (* Need to extend the context once for each constr.params, and then twice for
           each constr.args (twice, because of i.h.). *)
        let cx', nms, cvs, rvs, rs = build_cx cx D.Env.emp (Emp, Emp, Emp, Emp) constr.const_specs constr.rec_specs constr.dim_specs in
        let intro = V.make_intro (D.Env.clear_locals @@ Cx.env cx) ~dlbl:info.dlbl ~clbl:lbl ~const_args:cvs ~rec_args:rvs ~rs in
        let ty = V.inst_clo mot_clo intro in

        let image_of_face face =
          let elim_face r r' scrut =
            let phi = I.equate r r' in
            let mot = D.Clo.act phi mot_clo in
            let clauses = List.map (fun (lbl, nclo) -> lbl, D.NClo.act phi nclo) earlier_clauses in
            V.elim_data info.dlbl ~mot ~scrut ~clauses
          in
          Face.map elim_face @@
          let env0 = D.Env.clear_locals (Cx.env cx) in
          V.eval_bterm_face info.dlbl desc env0 face
            ~const_args:cvs
            ~rec_args:rvs
            ~rs:rs
        in
        let boundary = List.map image_of_face constr.boundary in
        check_boundary cx' ty boundary bdy;
        Tm.NB (nms, bdy)
      in

      let rec check_clauses acc constrs =
        match constrs with
        | [] ->
          ()
        | (lbl, constr) :: constrs ->
          let nbnd = check_clause acc lbl constr in
          let nclo = D.NClo {nbnd; rho = Cx.env cx} in
          check_clauses ((lbl, nclo) :: acc) constrs

      in

      check_clauses [] desc.constrs;
      D.{el = Cx.eval_frame cx ih.el frm; ty = V.inst_clo mot_clo ih.el}


    | T.Cap info ->
      let fhcom_ty =
        check_eval_ty cx @@
        T.make @@ T.FHCom {r = info.r; r' = info.r; cap = info.ty; sys = info.sys}
      in
      let ih = infer_spine cx hd sp in
      Cx.check_eq_ty cx fhcom_ty ih.ty;
      D.{el = Cx.eval_frame cx ih.el frm; ty = Cx.eval cx info.ty}


    | T.LblCall ->
      let ih = infer_spine cx hd sp in
      let _, _, ty = V.unleash_lbl_ty ih.ty in
      D.{el = Cx.eval_frame cx ih.el frm; ty}

    | Tm.CoRForce ->
      let ih = infer_spine cx hd sp in
      begin
        match V.unleash_corestriction_ty ih.ty with
        | Face.True (_, _, ty) ->
          D.{el = Cx.eval_frame cx ih.el frm; ty}
        | _ -> failwith "Cannot force co-restriction when it is not true!"
      end

    | T.Prev tick ->
      check_tick cx tick;
      let vtick = Cx.eval_tick cx tick in
      begin
        match vtick with
        | D.TickConst ->
          let cx' = Cx.ext_lock cx in
          let ih = infer_spine cx' hd sp in
          let tclo = V.unleash_later ih.ty in
          D.{el = V.prev vtick ih.el; ty = V.inst_tick_clo tclo vtick}
        | D.TickGen tgen ->
          let cx' = Cx.kill_from_tick cx tgen in
          let ih = infer_spine cx' hd sp in
          let tclo = V.unleash_later ih.ty in
          D.{el = V.prev vtick ih.el; ty = V.inst_tick_clo tclo vtick}
      end

    | T.Open ->
      let cx' = Cx.clear_locks cx in
      let ih = infer_spine cx' hd sp in
      let ty = V.unleash_box_modality ih.ty in
      D.{el = V.modal_open ih.el; ty}


and infer_head cx =
  function
  | T.Var {name; twin; ushift} ->
    let ty = Tm.shift_univ ushift @@ Cx.lookup_constant name twin cx in
    Cx.eval (Cx.clear_locals cx) ty

  | T.Ix (ix, _) ->
    begin
      match Cx.lookup ix cx with
      | `Ty ty -> ty
      | (`I | `Tick) -> failwith "infer: expected type hypothesis"
    end

  | T.Meta {name; ushift} ->
    let ty = Tm.shift_univ ushift @@ Cx.lookup_constant name `Only cx in
    Cx.eval (Cx.clear_locals cx) ty

  | T.Coe info ->
    let r = check_eval_dim cx info.r in
    let r' = check_eval_dim cx info.r' in
    let T.B (nm, ty) = info.ty in
    let cxx, x = Cx.ext_dim cx ~nm in
    let vtyx = check_eval_ty cxx ty in
    let vtyr = D.Value.act (I.subst r x) vtyx in
    check cx vtyr info.tm;
    D.Value.act (I.subst r' x) vtyx

  | T.Com info ->
    let r = check_eval_dim cx info.r in
    let r' = check_eval_dim cx info.r' in
    let T.B (nm, ty) = info.ty in
    let cxx, x = Cx.ext_dim cx ~nm in
    let vtyx = check_eval_ty cxx ty in
    let vtyr = D.Value.act (I.subst r x) vtyx in
    let cap = check_eval cx vtyr info.cap in
    check_valid_cofibration @@ cofibration_of_sys cx info.sys;
    check_comp_sys cx r (cxx, x, vtyx) cap info.sys;
    D.Value.act (I.subst r' x) vtyx

  | T.HCom info ->
    let r = check_eval_dim cx info.r in
    check_dim cx info.r';
    let cxx, x = Cx.ext_dim cx ~nm:None in
    let vty = check_eval_ty cx info.ty in
    let cap = check_eval cx vty info.cap in
    check_valid_cofibration @@ cofibration_of_sys cx info.sys;
    check_comp_sys cx r (cxx, x, vty) cap info.sys;
    vty

  | T.GCom info ->
    let r = check_eval_dim cx info.r in
    let r' = check_eval_dim cx info.r' in
    let T.B (nm, ty) = info.ty in
    let cxx, x = Cx.ext_dim cx ~nm in
    let vtyx = check_eval_ty cxx ty in
    let vtyr = D.Value.act (I.subst r x) vtyx in
    let cap = check_eval cx vtyr info.cap in
    check_comp_sys cx r (cxx, x, vtyx) cap info.sys;
    D.Value.act (I.subst r' x) vtyx

  | T.GHCom info ->
    let r = check_eval_dim cx info.r in
    check_dim cx info.r';
    let cxx, x = Cx.ext_dim cx ~nm:None in
    let vty = check_eval_ty cx info.ty in
    let cap = check_eval cx vty info.cap in
    check_comp_sys cx r (cxx, x, vty) cap info.sys;
    vty

  | T.Down info ->
    let ty = check_eval_ty cx info.ty in
    check cx ty info.tm;
    ty

  | T.DFix info ->
    check_dim cx info.r;
    let Tm.B (nm, bdy) = info.bdy in
    let ty = check_eval_ty cx info.ty in
    let ltr_ty = D.make_later ty in
    let cxx, _ = Cx.ext_ty cx ~nm ltr_ty in
    check cxx ty bdy;
    ltr_ty


and check_eval cx ty tm =
  check cx ty tm;
  Cx.eval cx tm

and check_ty cx ty =
  let univ = D.make @@ D.Univ {kind = Kind.Pre; lvl = Lvl.Omega} in
  check cx univ ty

and check_eval_dim cx tr =
  check_dim cx tr;
  Cx.eval_dim cx tr

and check_eval_ty cx ty =
  check_ty cx ty;
  Cx.eval cx ty

and check_is_equivalence cx ~ty0 ~ty1 ~equiv =
  let (module V) = Cx.evaluator cx in
  let type_of_equiv = V.Macro.equiv ty0 ty1 in
  check cx type_of_equiv equiv

let check_constr_boundary_sys cx dlbl desc sys =
  let rec go sys acc =
    match sys with
    | [] ->
      ()
    | (tr0, tr1, tm) :: sys ->
      let r0 = check_eval_dim cx tr0 in
      let r1 = check_eval_dim cx tr1 in
      begin
        match I.compare r0 r1 with
        | `Apart ->
          go sys acc

        | `Same | `Indet ->
          begin
            try
              let cx', _ = Cx.restrict cx r0 r1 in
              (* TODO: check boundary type *)
              (* check cx' (D.Value.act phi ty) tm; *)

              (* Check face-face adjacency conditions *)
              go_adj cx' acc (r0, r1, tm)
            with
            | I.Inconsistent -> ()
          end;
          go sys @@ (r0, r1, tm) :: acc
      end

  and go_adj cx faces face =
    match faces with
    | [] -> ()
    | (r'0, r'1, tm') :: faces ->
      (* Invariant: cx should already be restricted by r0=r1 *)
      let _r0, _r1, tm = face in
      begin
        try
          let cx', _ = Cx.restrict cx r'0 r'1 in
          let (module Q) = Cx.quoter cx' in
          let (module V) = Cx.evaluator cx' in
          let v = V.eval_bterm dlbl desc (Cx.env cx') tm in
          let v' = V.eval_bterm dlbl desc (Cx.env cx') tm' in
          (* let phi = I.cmp phi (I.equate r0 r1) in *)
          Q.equiv_boundary_value (Cx.qenv cx') dlbl desc Desc.Self v v'
        with
        | I.Inconsistent -> ()
      end;
      go_adj cx faces face
  in
  go sys []

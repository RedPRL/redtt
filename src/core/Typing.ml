module Q = Quote
module T = Tm
module D = Domain

open Tm.Notation

type value = D.value

type cx = Cx.t

open RedBasis
open Bwd
open BwdNotation

type cofibration = (I.t * I.t) list

type error =
  | ExpectedDimension of cx * Tm.tm
  | ExpectedTick of cx * Tm.tm
  | UnequalDimensions of I.t * I.t
  | TypeError of value * (cx * Tm.tm)

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
    | UnequalDimensions (i0, i1) ->
      Format.fprintf fmt
        "Unequal dimensions: %a /= %a"
        I.pp i0 I.pp i1
    | TypeError (ty, (cx, tm)) ->
      Format.fprintf fmt
        "Unable to show %a is of type %a."
        (Tm.pp (Cx.ppenv cx)) tm D.pp_value ty

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
  | hd, [] ->
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
      | Tm.DownX r ->
        check_dim cx r
      | _ -> failwith ""
    end
  | _ ->
    failwith "check_dim_cmd"

let rec check_tick cx tr =
  match T.unleash tr with
  | T.Up cmd ->
    check_tick_cmd cx cmd
  | _ ->
    raise @@ E (ExpectedTick (cx, tr))

and check_tick_cmd cx =
  function
  | hd, [] ->
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

let check_dim_scope xs =
  function
  | `Dim0 -> ()
  | `Dim1 -> ()
  | `Atom x -> if List.mem x xs then () else failwith "Bad dimension scope"

(* This is checking whether cofib is valid (forming a non-bipartite graph). *)
let check_valid_cofibration (cofib : (I.t * I.t) list) =
  (* the idea is to find an evil assignment (coloring) to make everything false *)
  let assignment = Hashtbl.create 10 in
  let adjacency = Hashtbl.create 20 in
  let rec color x b =
    Hashtbl.add assignment x b;
    let neighbors = Hashtbl.find_all adjacency x in
    let notb = not b in
    List.exists (fun y -> check_color y notb) neighbors
  and check_color x b =
    match Hashtbl.find_opt assignment x with
    | Some b' -> b' != b (* non-bipartite! *)
    | None -> color x b
  in
  let lookup_dim =
    function
    | `Dim0 -> `Assigned false
    | `Dim1 -> `Assigned true
    | `Atom x ->
      match Hashtbl.find_opt assignment x with
      | Some b -> `Assigned b
      | None -> `Atom x
  in
  let rec go eqns atoms_to_check =
    match eqns with
    | [] -> List.exists (fun x -> not (Hashtbl.mem assignment x) && color x true) atoms_to_check
    | (r, r') :: eqns ->
      match lookup_dim r, lookup_dim r' with
      | `Assigned b, `Assigned b' ->
        b = b' || (go[@tailcall]) eqns atoms_to_check
      | `Atom x, `Assigned b | `Assigned b, `Atom x ->
        color x (not b) || (go[@tailcall]) eqns atoms_to_check
      | `Atom x, `Atom y ->
        x = y ||
        begin
          Hashtbl.add adjacency x y;
          Hashtbl.add adjacency y x;
          (go[@tailcall]) eqns (x :: atoms_to_check)
        end
  in
  if go cofib [] then () else failwith "check_valid_cofibration"

let check_comp_cofibration _dir cofib =
  (* this might work, but needs more research:
   * check_valid_cofibration (dir :: cofib) *)
  check_valid_cofibration cofib

let check_extension_cofibration xs cofib =
  match cofib with
  | [] -> ()
  | _ ->
    List.iter (fun (r, r') -> check_dim_scope xs r; check_dim_scope xs r') cofib;
    check_valid_cofibration cofib

let rec check_ cx ty rst tm =
  let (module V) = Cx.evaluator cx in
  match rst, V.unleash ty, T.unleash tm with
  | [], D.Univ info0, T.Univ info1 ->
    (* TODO: what about kinds? I think it's fine, since we learned from Andy Pitts how to make
       the pretype universe Kan. But I may need to add those "ecom" thingies, LOL. *)
    if Lvl.greater info0.lvl info1.lvl then () else
      failwith "Predicativity violation"


  | [], D.Univ _, T.Pi (dom, B (nm, cod)) ->
    let vdom = check_eval cx ty dom in
    let cxx', _ = Cx.ext_ty cx ~nm vdom in
    check cxx' ty cod

  | [], D.Univ _, T.Sg (dom, B (nm, cod)) ->
    let vdom = check_eval cx ty dom in
    let cxx, _ = Cx.ext_ty cx ~nm vdom in
    check cxx ty cod

  | [], D.Univ _, T.Later (B (nm, cod)) ->
    let cxx, _ = Cx.ext_tick cx ~nm in
    check cxx ty cod

  | [], D.Univ univ, T.Ext (NB (nms, (cod, sys))) ->
    let cxx, xs = Cx.ext_dims cx ~nms:(Bwd.to_list nms) in
    let vcod = check_eval cxx ty cod in
    if Kind.lte univ.kind `Kan then
      check_extension_cofibration xs @@ cofibration_of_sys cxx sys
    else
      ();
    check_tm_sys cxx vcod sys

  | [], D.Univ univ, T.Restrict (tr, tr', oty) ->
    if univ.kind = `Pre then () else failwith "Co-restriction type is not known to be Kan";
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

  | [], D.Univ _, T.V info ->
    check_dim cx info.r;
    let ty0 = check_eval cx ty info.ty0 in
    let ty1 = check_eval cx ty info.ty1 in
    check_is_equivalence cx ~ty0 ~ty1 ~equiv:info.equiv

  | [], D.Univ univ, T.Data {lbl; params} ->
    let desc = GlobalEnv.lookup_datatype lbl @@ Cx.globals cx in
    check_data_params cx lbl desc.body params;
    begin
      if not @@ Lvl.lte desc.lvl univ.lvl && Kind.lte desc.kind univ.kind then
        failwith "Universe level/kind error";
      if desc.status = `Partial then
        failwith "Partially declared datatype cannot not be treated as type"
    end

  | [], D.Data data, T.Intro (dlbl, clbl, params, args) when data.lbl = dlbl ->
    let desc = GlobalEnv.lookup_datatype dlbl @@ Cx.globals cx in
    check_data_params cx dlbl desc.body params;
    let vparams = List.map (fun tm -> `Val (Cx.eval cx tm)) params in
    let (module Q) = Cx.quoter cx in
    Q.equiv_data_params (Cx.qenv cx) dlbl desc.body vparams data.params;
    let data_ty = Cx.quote_ty cx ty in
    let constr = Desc.lookup_constr clbl @@ Desc.Body.instance params desc.body in
    check_constr cx dlbl data.params constr args;

  | [], D.Data dlbl, T.FHCom info ->
    check_fhcom cx ty info.r info.r' info.cap info.sys


  | _, D.Pi {dom; cod}, T.Lam (T.B (nm, tm)) ->
    let cxx, x = Cx.ext_ty cx ~nm dom in
    let vcod = V.inst_clo cod x in
    let rst' = List.map (Face.map (fun r r' v -> V.apply v @@ D.Value.act (I.equate r r') x)) rst in
    check_ cxx vcod rst' tm

  | _, D.Later tclo, T.Next (T.B (nm, tm)) ->
    let cxx, tck = Cx.ext_tick cx ~nm in
    let vty = V.inst_tick_clo tclo tck in
    let rst' = List.map (Face.map (fun _ _ -> V.prev tck)) rst in
    check_ cxx vty rst' tm

  | _, D.Sg {dom; cod}, T.Cons (t0, t1) ->
    let rst0 = List.map (Face.map (fun _ _ -> V.do_fst)) rst in
    let rst1 = List.map (Face.map (fun _ _ -> V.do_snd)) rst in
    let v = check_eval_ cx dom rst0 t0 in
    let vcod = V.inst_clo cod v in
    check_ cx vcod rst1 t1

  | _, D.Ext ext_abs, T.ExtLam (T.NB (nms, tm)) ->
    let cxx, xs = Cx.ext_dims cx ~nms:(Bwd.to_list nms) in
    let codx, sysx = Domain.ExtAbs.inst ext_abs @@ Bwd.map (fun x -> `Atom x) @@ Bwd.from_list xs in
    let rst' = List.map (Face.map (fun _ _ el -> V.ext_apply el @@ List.map (fun x -> `Atom x) xs)) rst in
    check_ cxx codx (rst' @ sysx) tm

  | _, D.Ext ext_abs, T.Up cmd ->
    let n = D.ExtAbs.len ext_abs in
    let nms =
      let xs, _ = D.ExtAbs.unleash ext_abs in
      List.map Name.name @@ Bwd.to_list xs
    in
    let cxx, xs = Cx.ext_dims cx ~nms in
    let rs = List.map (fun x -> `Atom x) xs in
    let trs = List.map (Cx.quote_dim cxx) rs in
    let codx, sysx = Domain.ExtAbs.inst ext_abs @@ Bwd.from_list rs in
    let cmd' = T.subst_cmd (T.shift n) cmd in
    let rst' = List.map (Face.map (fun _ _ el -> V.ext_apply el rs)) rst in
    check_ cxx codx (rst' @ sysx) @@ Tm.up @@ cmd' @< Tm.ExtApp trs

  | _, D.Restrict ty_face, T.RestrictThunk (tr0, tr1, otm) ->
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
            let rst' = List.map (Face.map (fun _ _ -> V.restriction_force)) rst in
            check_ cx (Lazy.force ty) rst' tm
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
                (* is this right?? : *)
                let rst' = List.map (Face.map (fun _ _ -> V.restriction_force)) rst in
                check_ cx' (Domain.Value.act phi @@ Lazy.force ty) rst' tm
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

  | [], D.Univ _, T.FHCom info ->
    check_fhcom cx ty info.r info.r' info.cap info.sys


  | [], D.Univ _, T.LblTy info ->
    check cx ty info.ty;
    let go_arg (ty, tm) =
      let vty = check_eval_ty cx ty in
      check cx vty tm
    in
    List.iter go_arg info.args

  | [], D.LblTy info, T.LblRet t ->
    let rst' = List.map (Face.map (fun _ _ -> V.lbl_call)) rst in
    check_ cx info.ty rst' t

  | [], D.V vty, T.VIn vin ->
    let r = check_eval_dim cx vin.r in
    begin
      match I.compare (`Atom vty.x) r with
      | `Same ->
        let cx', phi = Cx.restrict cx (`Atom vty.x) `Dim0 in
        let el0 = check_eval cx' vty.ty0 vin.tm0 in
        let el1 = check_eval cx vty.ty1 vin.tm1 in
        Cx.check_eq cx' ~ty:(D.Value.act phi vty.ty1) (V.apply (V.do_fst vty.equiv) el0) @@ D.Value.act phi el1
      | _ ->
        failwith "v/vin dimension mismatch"
    end;

  | [], D.FHCom tyinfo, T.Box tinfo ->
    check_box cx tyinfo.dir tyinfo.cap tyinfo.sys tinfo.r tinfo.r' tinfo.cap tinfo.sys

  | [], _, T.Up tm ->
    let ty' = infer cx tm in
    Cx.check_subtype cx ty' ty

  | _, _, T.Let (cmd, T.B (nm, t1)) ->
    let ty' = infer cx cmd in
    let el = Cx.eval_cmd cx cmd in
    let cx' = Cx.def cx ~nm ~ty:ty' ~el in
    (* TODO: right?? *)
    check_ cx' ty rst t1


  | _ :: _, _, _ ->
    let v = check_eval cx ty tm in
    check_boundary cx ty rst v

  | [], _, _ ->
    raise @@ E (TypeError (ty, (cx, tm)))

and check_data_params cx _dlbl tele params =
  let (module V) = Cx.evaluator cx in
  let rec go tyenv tele params =
    match tele, params with
    | Desc.TNil _, [] ->
      ()

    | Desc.TCons (ty, Tm.B (nm, tele)), tm :: params ->
      let vty = V.eval tyenv ty in
      let el = check_eval cx vty tm in
      let tyenv = D.Env.snoc tyenv (`Val el) in
      go tyenv tele params

    | _ ->
      failwith "check_data_params: length mismatch"
  in
  go (Cx.env cx) tele params

and check cx ty tm =
  check_ cx ty [] tm


and check_constr cx dlbl params constr tms =
  let vdataty = D.make @@ D.Data {lbl = dlbl; params} in
  let (module V) = Cx.evaluator (Cx.clear_locals cx) in


  let check_argument tyenv spec tm =
    match spec with
    | `Const ty ->
      let vty = V.eval tyenv ty in
      let el = check_eval cx vty tm in
      D.Env.snoc tyenv @@ `Val el
    | `Rec Desc.Self ->
      let el = check_eval cx vdataty tm in
      D.Env.snoc tyenv @@ `Val el
    | `Dim ->
      let r = check_eval_dim cx tm in
      D.Env.snoc tyenv @@ `Dim r
  in

  let _ : D.env =
    List.fold_right2
      (fun (_, spec) tm tyenv -> check_argument tyenv spec tm)
      (Desc.Constr.specs constr)
      tms
      V.empty_env
  in
  ()

and cofibration_of_sys : type a. cx -> (Tm.tm, a) Tm.system -> cofibration =
  fun cx sys ->
    let face (tr, tr', _) =
      let r = Cx.eval_dim cx tr in
      let r' = Cx.eval_dim cx tr' in
      (r, r')
    in
    List.map face sys

(* XXX the following code smells! *)
and check_box cx tydir tycap tysys tr tr' tcap tsys =
  let raiseError () =
    let ty = D.make @@ D.FHCom {dir=tydir; cap=tycap; sys=tysys} in
    let tm = Tm.make @@ Tm.Box {r=tr; r'=tr'; cap=tcap; sys=tsys} in
    raise @@ E (TypeError (ty, (cx, tm)))
  in
  let tyr, tyr' = Dir.unleash tydir in
  let r = check_eval_dim cx tr in
  Cx.check_eq_dim cx tyr r;
  let r' = check_eval_dim cx tr' in
  Cx.check_eq_dim cx tyr' r';
  let cap = check_eval cx tycap tcap in
  let rec go tysys tsys acc =
    match tsys with
    | [] -> if tysys = [] then () else raiseError ()
    | (tri0, tri1, otm) :: tsys ->
      let ri0 = check_eval_dim cx tri0 in
      let ri1 = check_eval_dim cx tri1 in
      match tysys, I.compare ri0 ri1, otm with
      | _, `Apart, _ ->
        (* skipping false boundaries without consuming `tysys`. *)
        go tysys tsys acc

      | _, `Same, _ ->
        raiseError ()

      | (Face.Indet (p, tyabs) :: tysys), `Indet, Some tm ->
        let tyri0, tyri1 = Eq.unleash p in
        Cx.check_eq_dim cx tyri0 ri0;
        Cx.check_eq_dim cx tyri1 ri1;

        begin
          try
            let cx, phi = Cx.restrict cx ri0 ri1 in
            let (module V) = Cx.evaluator cx in
            let tyabs = Lazy.force tyabs in
            let ty_r' = D.Abs.inst1 tyabs tyr' in
            let el = check_eval cx ty_r' tm in
            Cx.check_eq cx ~ty:(D.Value.act phi tycap)
              (D.Value.act phi cap)
              (V.make_coe (Dir.act phi (Dir.swap tydir)) tyabs el);

            (* Check face-face adjacency conditions *)
            go_adj cx ty_r' acc (ri0, ri1, el);
            go tysys tsys @@ (ri0, ri1, el) :: acc
          with
          | I.Inconsistent -> raiseError ()
        end
      | _ ->
        raiseError ()

  and go_adj cx ty faces (ri0, ri1, el) : unit =
    match faces with
    | [] -> ()
    | (ri'0, ri'1, el') :: faces ->
      (* Invariant: cx, ty and el should already be restricted by ri0=ri1,
       * and el' should already be restricted by ri'0=ri'1. *)
      begin
        try
          let phi' =
            let ri0 = I.act (I.equate ri'0 ri'1) ri0 in
            let ri1 = I.act (I.equate ri'0 ri'1) ri1 in
            I.equate ri0 ri1
          in
          let cx, phi =
            let ri'0 = I.act (I.equate ri0 ri1) ri'0 in
            let ri'1 = I.act (I.equate ri0 ri1) ri'1 in
            Cx.restrict cx ri'0 ri'1
          in
          Cx.check_eq cx ~ty:(D.Value.act phi ty) (D.Value.act phi el) (D.Value.act phi' el')
        with
        | I.Inconsistent -> ()
      end;
      go_adj cx ty faces (ri0, ri1, el)
  in
  go tysys tsys []

and check_fhcom cx ty tr tr' tcap tsys =
  let r = check_eval_dim cx tr in
  let r' = check_eval_dim cx tr' in
  let cxx, x = Cx.ext_dim cx ~nm:None in
  let cap = check_eval cx ty tcap in
  check_comp_cofibration (r, r') @@ cofibration_of_sys cx tsys;
  check_comp_sys cx r (cxx, x, ty) cap tsys

and check_boundary cx ty sys el =
  let rec go sys =
    match sys with
    | [] -> ()
    | face :: sys ->
      check_boundary_face cx ty face el;
      go sys
  in
  go sys

and check_boundary_face cx ty face el =
  match face with
  | Face.True (_, _, el') ->
    Cx.check_eq cx ~ty (Lazy.force el') el

  | Face.False _ ->
    ()

  | Face.Indet (p, el') ->
    let r, r' = Eq.unleash p in
    try
      let cx', phi = Cx.restrict cx r r' in
      Cx.check_eq cx' ~ty:(D.Value.act phi ty) (Lazy.force el') @@ D.Value.act phi el
    with
    | I.Inconsistent ->
      ()

and check_tm_sys cx ty sys =
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
          failwith "check_tm_sys"
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

and infer_spine_ cx hd sp =
  let (module V) = Cx.evaluator cx in
  match sp with
  | Emp ->
    let vhd = Cx.eval_head cx hd in
    let ty = infer_head cx hd in
    D.{el = vhd; ty}

  | Snoc (sp, frm) ->
    match frm with
    | T.Fst ->
      let ih = infer_spine_ cx hd sp in
      let dom, _ = V.unleash_sg ih.ty in
      D.{el = V.do_fst ih.el; ty = dom}

    | T.Snd ->
      let ih = infer_spine_ cx hd sp in
      let _, cod = V.unleash_sg ih.ty in
      let car = V.do_fst ih.el in
      D.{el = V.do_snd ih.el; ty = V.inst_clo cod car}

    | T.FunApp t ->
      let ih = infer_spine_ cx hd sp in
      let dom, cod = V.unleash_pi ih.ty in
      let v = check_eval cx dom t in
      D.{el = V.apply ih.el v; ty = V.inst_clo cod v}

    | T.ExtApp ts ->
      let ih = infer_spine_ cx hd sp in
      let rs = List.map (check_eval_dim cx) ts in
      let ty, _ = V.unleash_ext_with ih.ty rs in
      D.{el = V.ext_apply ih.el rs; ty}

    | T.VProj info ->
      let ih = infer_spine_ cx hd sp in
      let x, ty0, ty1, equiv = V.unleash_v ih.ty in
      let func' = V.do_fst equiv in
      let func_ty = D.Value.act (I.subst `Dim0 x) @@ V.Macro.func ty0 ty1 in
      let func = check_eval cx func_ty info.func in
      Cx.check_eq cx ~ty:func_ty func func';
      D.{el = Cx.eval_frame cx ih.el frm; ty = ty1}

    | T.Elim info ->
      let vparams = List.map (fun tm -> `Val (Cx.eval cx tm)) info.params in
      let T.B (nm, mot) = info.mot in
      let ih = infer_spine_ cx hd sp in
      let mot_clo =
        let cxx, _= Cx.ext_ty cx ~nm ih.ty in
        check_ty cxx mot;
        Cx.make_closure cx info.mot
      in

      let desc = V.Sig.lookup_datatype info.dlbl in
      let constrs = Desc.Body.instance info.params desc.body in

      if desc.status = `Partial then failwith "Cannot call eliminator on partially-defined datatype";

      let used_labels = Hashtbl.create 10 in


      let check_clause nclos lbl constr =
        if Hashtbl.mem used_labels lbl then failwith "Duplicate case in eliminator";
        Hashtbl.add used_labels lbl ();
        let _, Tm.NB (_, bdy) = List.find (fun (lbl', _) -> lbl = lbl') info.clauses in

        let rec go cx venv cells_only_ihs cells_w_ihs cells specs =
          match specs with
          | (lbl, `Const ty) :: specs ->
            let vty = V.eval venv ty in
            let cx, v = Cx.ext_ty cx ~nm:lbl vty in
            let venv = D.Env.snoc venv @@ `Val v in
            go cx venv (cells_only_ihs #< (`Val v)) (cells_w_ihs #< (`Val v)) (cells #< (`Val v)) specs

          | (lbl, `Rec Desc.Self) :: specs ->
            let vty = D.make @@ D.Data {lbl = info.dlbl; params = vparams} in
            let cx, v = Cx.ext_ty cx ~nm:lbl vty in
            let cx_ih, v_ih = Cx.ext_ty cx ~nm:None @@ V.inst_clo mot_clo v in
            let venv = D.Env.snoc venv @@ `Val v in
            go cx_ih venv (cells_only_ihs #< (`Val v_ih)) (cells_w_ihs <>< [`Val v; `Val v_ih]) (cells #< (`Val v)) specs

          | (lbl, `Dim) :: specs ->
            let x = Name.named lbl in
            let r = `Atom x in
            let cx = Cx.def_dim cx ~nm:lbl r in
            let venv = D.Env.snoc venv @@ `Dim r in
            go cx venv (cells_only_ihs #< (`Dim r)) (cells_w_ihs #< (`Dim r)) (cells #< (`Dim r)) specs

          | [] ->
            cx, Bwd.to_list cells_only_ihs, Bwd.to_list cells_w_ihs, Bwd.to_list cells
        in

        let cx', cells_only_ihs, cells_w_ihs, cells = go cx (D.Env.append V.empty_env vparams) Emp Emp Emp @@ Desc.Constr.specs constr in
        let generic_intro = V.make_intro (D.Env.clear_locals @@ Cx.env cx) ~dlbl:info.dlbl ~params:vparams ~clbl:lbl cells in

        (* maybe wrong *)

        let rec image_of_bterm phi tm =
          let benv = D.Env.append V.empty_env cells in
          match Tm.unleash tm with
          | Tm.Intro (_, clbl, params, args) ->
            let constr = Desc.lookup_constr clbl constrs in
            let nclo : D.nclo = D.NClo.act phi @@ snd @@ List.find (fun (clbl', _) -> clbl' = clbl) nclos in
            let rec go specs tms =
              match specs, tms with
              | (_, `Const ty) :: specs, tm :: tms ->
                `Val (D.Value.act phi @@ V.eval benv tm) :: go specs tms
              | (_, `Rec Desc.Self) :: specs, tm :: tms ->
                `Val (D.Value.act phi @@ V.eval benv tm) :: `Val (image_of_bterm phi tm) :: go specs tms
              | (_, `Dim) :: specs, tm :: tms ->
                `Dim (I.act phi @@ V.eval_dim benv tm) :: go specs tms
              | [], [] ->
                []
              | _ ->
                failwith "image_of_bterm"
            in
            V.inst_nclo nclo @@ go (Desc.Constr.specs constr) args
          | _ ->
            D.Value.act phi @@ V.eval (D.Env.append V.empty_env cells_only_ihs) tm

        in

        let image_of_bface (tr, tr', otm) =
          let benv = D.Env.append V.empty_env cells_only_ihs in
          let r = V.eval_dim benv tr in
          let r' = V.eval_dim benv tr' in
          D.ValFace.make I.idn r r' @@ fun phi ->
          let tm = Option.get_exn otm in
          image_of_bterm phi tm
        in

        let ty = V.inst_clo mot_clo generic_intro in

        let boundary = List.map image_of_bface @@ Desc.Constr.boundary constr in
        check_ cx' ty boundary bdy;

        let nms = Bwd.map (fun _ -> None) @@ Bwd.from_list cells_w_ihs in

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

      check_clauses [] constrs;
      D.{el = Cx.eval_frame cx ih.el frm; ty = V.inst_clo mot_clo ih.el}


    | T.Cap info ->
      let fhcom_ty =
        check_eval_ty cx @@
        T.make @@ T.FHCom {r = info.r; r' = info.r; cap = info.ty; sys = info.sys}
      in
      let ih = infer_spine_ cx hd sp in
      Cx.check_eq_ty cx fhcom_ty ih.ty;
      D.{el = Cx.eval_frame cx ih.el frm; ty = Cx.eval cx info.ty}


    | T.LblCall ->
      let ih = infer_spine_ cx hd sp in
      let _, _, ty = V.unleash_lbl_ty ih.ty in
      D.{el = Cx.eval_frame cx ih.el frm; ty}

    | Tm.RestrictForce ->
      let ih = infer_spine_ cx hd sp in
      begin
        match V.unleash_restriction_ty ih.ty with
        | Face.True (_, _, ty) ->
          D.{el = Cx.eval_frame cx ih.el frm; ty = Lazy.force ty}
        | _ -> failwith "Cannot force co-restriction when it is not true!"
      end

    | T.Prev tick ->
      check_tick cx tick;
      let vtick = Cx.eval_tick cx tick in
      begin
        match vtick with
        | D.TickGen tgen ->
          let cx' = Cx.kill_from_tick cx tgen in
          let ih = infer_spine_ cx' hd sp in
          let tclo = V.unleash_later ih.ty in
          D.{el = V.prev vtick ih.el; ty = V.inst_tick_clo tclo vtick}
      end

and infer_spine cx hd sp =
  infer_spine_ cx hd @@ Bwd.from_list sp

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
    check_comp_cofibration (r, r') @@ cofibration_of_sys cx info.sys;
    check_comp_sys cx r (cxx, x, vtyx) cap info.sys;
    D.Value.act (I.subst r' x) vtyx

  | T.HCom info ->
    let r = check_eval_dim cx info.r in
    let r' = check_eval_dim cx info.r' in
    let cxx, x = Cx.ext_dim cx ~nm:None in
    let vty = check_eval_ty cx info.ty in
    let cap = check_eval cx vty info.cap in
    check_comp_cofibration (r, r') @@ cofibration_of_sys cx info.sys;
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

  | T.DownX _ ->
    failwith "infer_head/DownX"

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

and check_eval_ cx ty rst tm =
  check_ cx ty rst tm;
  Cx.eval cx tm

and check_ty cx ty =
  let univ = D.make @@ D.Univ {kind = `Pre; lvl = `Omega} in
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

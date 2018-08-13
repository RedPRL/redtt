(* Experimental code *)
open RedTT_Core
open RedBasis
open Bwd open BwdNotation

module type Import =
sig
  val import : Lwt_io.file_name -> [`Elab of ESig.esig | `Cached]
end

module Make (I : Import) =
struct

  module C = Contextual
  module U = Unify

  open Dev open Unify

  module M = ElabMonad
  module Notation = Monad.Notation (M)
  open Notation

  open Tm.Notation

  let rec traverse f xs =
    match xs with
    | [] ->
      M.ret []
    | x :: xs ->
      (fun y ys -> y :: ys) <@>> f x <*> traverse f xs

  module E = ESig
  module T = Map.Make (String)

  open Refiner

  type mode =
    | Chk of ty
    | Inf

  let univ = Tm.univ ~lvl:`Omega ~kind:`Pre

  let get_resolver env =
    let rec go_globals renv  =
      function
      | [] -> renv
      | (name, x) :: env ->
        let renvx = ResEnv.global name x renv in
        go_globals renvx env
    in
    let rec go_locals renv =
      function
      | Emp -> renv
      | Snoc (psi, (x, _)) ->
        let renv = go_locals renv psi in
        begin
          match Name.name x with
          | Some str ->
            ResEnv.global str x renv
          | None ->
            renv
        end
    in
    M.lift C.ask <<@> fun psi ->
      let renv = go_globals (ResEnv.init ()) @@ T.bindings env in
      go_locals renv psi

  let (<+>) m n =
    M.optional m >>= function
    | Some x -> M.ret x
    | None -> n


  let kind_of_frame env =
    function
    | E.App ({con = E.TickConst} as e) ->
      M.ret @@ `Prev e
    | E.App ({con = E.Num (0 | 1)} as e) ->
      M.ret @@ `ExtApp e
    | E.App ({con = E.Var (nm, _)} as e) ->
      get_resolver env >>= fun renv ->
      begin
        try
          begin
            match ResEnv.get nm renv with
            | `Var alpha ->
              M.lift C.get_global_env >>= fun env ->
              begin
                match GlobalEnv.lookup_kind env alpha with
                | `P _ -> M.ret @@ `FunApp e
                | `Tw _ -> M.ret @@ `FunApp e
                | `I -> M.ret @@ `ExtApp e
                | `Tick -> M.ret @@ `Prev e
              end
            | _ ->
              failwith "kind_of_frame"
          end
        with _ -> M.ret @@ `FunApp e
      end
    | E.App e ->
      M.ret @@ `FunApp e
    | E.Car ->
      M.ret `Car
    | E.Cdr ->
      M.ret `Cdr
    | E.Open ->
      M.ret `Open



  let rec elab_sig env =
    function
    | [] ->
      M.ret env
    | E.Debug f :: esig ->
      elab_decl env @@ E.Debug f >>= fun env' ->
      elab_sig env' esig
    | E.Quit :: _ ->
      M.ret env
    | dcl :: esig ->
      elab_decl env dcl >>= fun env' ->
      elab_sig env' esig


  and elab_decl env =
    function
    | E.Define (name, opacity, scheme, e) ->
      let now0 = Unix.gettimeofday () in
      elab_scheme env scheme @@ fun cod ->
      M.unify >>
      elab_chk env cod e >>= fun tm ->
      let alpha = Name.named @@ Some name in

      M.lift C.ask >>= fun psi ->
      M.lift @@ U.define psi alpha opacity cod tm >>= fun _ ->
      M.lift C.go_to_top >>
      M.unify <<@> fun _ ->
        let now1 = Unix.gettimeofday () in
        Format.printf "Defined %s (%fs).@." name (now1 -. now0);
        T.add name alpha env

    | E.Data (dlbl, edesc) ->
      elab_datatype env dlbl edesc >>= fun desc ->
      M.lift @@ C.global (GlobalEnv.declare_datatype dlbl desc) >>
      M.ret env

    | E.Debug filter ->
      let title =
        match filter with
        | `All -> "Development state:"
        | `Constraints -> "Unsolved constraints:"
        | `Unsolved -> "Unsolved entries:"
      in
      M.lift @@ C.dump_state Format.std_formatter title filter >>
      M.ret env

    | E.Import file_name ->
      begin
        match I.import file_name with
        | `Cached ->
          M.ret env
        | `Elab esig ->
          elab_sig env esig
      end

    | E.Quit ->
      M.ret env

  and elab_datatype env dlbl edesc =
    let rec go acc eparams econstrs =
      match eparams, econstrs with
      | (_lbl, _epty) :: _eparams, _ ->
        failwith "elab_datatype"

      | [], [] -> M.ret acc

      | [], econstr :: econstrs ->
        elab_constr env dlbl acc econstr >>= fun constr ->
        go Desc.{acc with constrs = acc.constrs @ [constr]} eparams econstrs
    in
    match edesc.kind with
    | `Reg ->
      failwith "elab_datatype: Not yet sure what conditions need to be checked for `Reg kind"
    | _ ->
      go Desc.{edesc with constrs = []; params = []} edesc.params edesc.constrs

  and elab_constr env dlbl desc (clbl, constr) =
    if List.exists (fun (lbl, _) -> clbl = lbl) desc.constrs then
      failwith "Duplicate constructor in datatype";

    let open Desc in
    let elab_rec_spec (x, Self) = M.ret (x, Self) in

    let rec abstract_tele xs =
      function
      | [] -> []
      | (lbl, x, ty) :: const_specs ->
        let Tm.NB (_, ty') = Tm.bindn xs ty in
        (lbl, ty') :: abstract_tele (xs #< x) const_specs
    in

    let rec go acc =
      function
      | [] ->
        let const_specs = abstract_tele Emp @@ Bwd.to_list acc in
        (* TODO: when self args are more complex, we'll need to abstract them over
           the parameters too. *)
        traverse elab_rec_spec constr.rec_specs >>= fun rec_specs ->

        let psi =
          List.map (fun (nm, ty) -> (Name.named @@ Some nm, `SelfArg ty)) rec_specs
          @ List.map (fun nm -> (Name.named @@ Some nm, `I)) constr.dim_specs
        in
        M.in_scopes psi @@
        begin
          elab_constr_boundary env dlbl desc (const_specs, rec_specs, constr.dim_specs) constr.boundary >>= fun boundary ->
          M.ret
            (clbl,
             {const_specs = abstract_tele Emp @@ Bwd.to_list acc;
              rec_specs;
              dim_specs = constr.dim_specs;
              boundary})
        end

      | (lbl, ety) :: const_specs ->
        (* TODO: support higher universes *)
        let univ = Tm.univ ~kind:desc.kind ~lvl:desc.lvl in
        elab_chk env univ ety >>= bind_in_scope >>= fun pty ->
        let x = Name.named @@ Some lbl in
        M.in_scope x (`P pty) @@
        go (acc #< (lbl, x, pty)) const_specs
    in

    go Emp constr.const_specs

  and elab_constr_boundary env dlbl desc (const_specs, rec_specs, dim_specs) sys : (Tm.tm, Tm.tm Desc.Boundary.term) Desc.Boundary.sys M.m =
    M.lift C.base_cx >>= fun cx ->
    let (module V) = Cx.evaluator cx in
    let module D = Domain in

    let rec build_cx cx env (nms, cvs, rvs, rs) const_specs rec_specs dim_specs =
      match const_specs, rec_specs, dim_specs with
      | (plbl, pty) :: const_specs, _, _ ->
        let vty = V.eval env pty in
        let cx', v = Cx.ext_ty cx ~nm:(Some plbl) vty in
        build_cx cx' (D.Env.push (`Val v) env) (nms #< (Some plbl), cvs #< v, rvs, rs) const_specs rec_specs dim_specs
      | [], (nm, Desc.Self) :: rec_specs, _ ->
        let cx_x, v_x = Cx.ext_ty cx ~nm:(Some nm) @@ D.make @@ D.Data dlbl in
        build_cx cx_x env (nms #< (Some nm), cvs, rvs #< v_x, rs) const_specs rec_specs dim_specs
      | [], [], nm :: dim_specs ->
        let cx', x = Cx.ext_dim cx ~nm:(Some nm) in
        build_cx cx' env (nms #< (Some nm), cvs, rvs, rs #< (`Atom x)) const_specs rec_specs dim_specs
      | [], [], [] ->
        cx
    in

    let cx' = build_cx cx D.Env.emp (Emp, Emp, Emp, Emp) const_specs rec_specs dim_specs in
    traverse (elab_constr_face env dlbl desc) sys >>= fun bdry ->
    Typing.check_constr_boundary_sys cx' dlbl desc bdry;
    M.ret bdry

  and elab_constr_face env dlbl desc (er0, er1, e) =
    elab_dim env er0 >>= bind_in_scope >>= fun r0 ->
    elab_dim env er1 >>= bind_in_scope >>= fun r1 ->
    M.in_scope (Name.fresh ()) (`R (r0, r1)) @@
    begin
      elab_boundary_term env dlbl desc e <<@> fun bt ->
        r0, r1, bt
    end

  and elab_boundary_term env dlbl desc e =
    match e.con with
    | E.Var (nm, _) ->
      elab_boundary_cut env dlbl desc nm Emp
    | E.Cut ({con = E.Var (nm, _)}, spine) ->
      elab_boundary_cut env dlbl desc nm spine
    | _ ->
      failwith "TODO: elaborate_boundary_term"

  and boundary_resolve_name env desc name =
    let open Desc in
    begin
      get_resolver env >>= fun renv ->
      match ResEnv.get name renv with
      | `Var x ->
        M.lift C.ask >>= fun psi ->
        (* backwards? *)
        let ix = ListUtil.index_of (fun (y, _) -> x = y) @@ Bwd.to_list psi in
        M.ret @@ `Ix ix
      | `Ix _ ->
        failwith "impossible"
    end
    <+>
    begin
      M.ret () >>= fun _ ->
      M.ret @@ `Constr (List.find (fun (lbl, _) -> name = lbl) desc.constrs)
    end

  and elab_boundary_cut env dlbl desc name spine =
    boundary_resolve_name env desc name >>= function
    | `Ix ix ->
      begin
        match spine with
        | Emp ->
          M.ret @@ Desc.Boundary.Var ix
        | _ ->
          failwith "elab_boundary_cut: non-empty spine not yet supported"
      end

    | `Constr (clbl, constr) ->
      let rec go_const_specs acc ps frms =
        match ps, frms with
        | [], _ ->
          M.ret (List.rev_map snd acc, frms)
        | (_, pty) :: ps, E.App e :: frms ->
          (* TODO: might be backwards *)
          let sub = List.fold_right (fun (ty,tm) sub -> Tm.dot (Tm.ann ~ty ~tm) sub) acc @@ Tm.shift 0 in
          let pty' = Tm.subst sub pty in
          elab_chk env pty' e >>= bind_in_scope >>= fun t ->
          go_const_specs ((pty', t) :: acc) ps frms
        | _ ->
          failwith "elab_intro: malformed parameters"
      in

      let rec go_args acc rec_specs frms =
        match rec_specs, frms with
        | [], _ ->
          M.ret (Bwd.to_list acc, frms)
        | (_, Desc.Self) :: rec_specs, E.App e :: frms ->
          elab_boundary_term env dlbl desc e >>= fun bt ->
          go_args (acc #< bt) rec_specs frms
        | _ ->
          failwith "todo: go_args"
      in

      let rec go_dims acc dim_specs frms =
        match dim_specs, frms with
        | [], [] ->
          M.ret @@ Bwd.to_list acc
        | _ :: dim_specs, E.App e :: frms ->
          elab_dim env e >>= bind_in_scope >>= fun r ->
          go_dims (acc #< r) dim_specs frms
        | _ ->
          failwith "Dimensions length mismatch in boundary term"
      in

      go_const_specs [] constr.const_specs @@ Bwd.to_list spine >>= fun (const_args, frms) ->
      go_args Emp constr.rec_specs frms >>= fun (rec_args, frms) ->
      go_dims Emp constr.dim_specs frms >>= fun rs ->
      M.ret @@ Desc.Boundary.Intro {clbl; const_args; rec_args; rs}


  and bind_in_scope tm =
    M.lift C.ask <<@> fun psi ->
      let go (x, param) =
        match param with
        | `P _ -> [x]
        | `I -> [x]
        | `SelfArg _ -> [x]
        | `Tick -> [x]
        | `Tw _ -> []
        | _ -> []
      in
      let xs = Bwd.rev @@ Bwd.flat_map go psi in
      let Tm.NB (_, tm) = Tm.bindn xs tm in
      tm



  and elab_scheme env (cells, ecod) kont =
    let rec go =
      function
      | [] ->
        elab_chk env univ ecod >>=
        kont
      | `Ty (name, edom) :: cells ->
        elab_chk env univ edom >>= normalize_ty >>= fun dom ->
        let x = Name.named @@ Some name in
        M.in_scope x (`P dom) @@
        go cells
      | `Tick name :: cells ->
        let x = Name.named @@ Some name in
        M.in_scope x `Tick @@
        go cells
      | `I name :: cells ->
        let x = Name.named @@ Some name in
        M.in_scope x `I @@
        go cells
      | `Lock :: cells ->
        let x = Name.fresh () in
        M.in_scope x `Lock @@
        go cells
      | _ -> failwith "TODO: elab_scheme"
    in
    go cells





  (* TODO: we will be disentangling all the elaboration of concrete expressions from tactics which produce redtt proofs.
     As an example, see what we have done with tac_lambda, tac_if, etc. *)
  and elab_chk env ty e : tm M.m =
    normalize_ty ty >>= fun ty ->
    match Tm.unleash ty, e.con with
    | Tm.Rst rst, E.Guess e ->
      elab_chk env rst.ty e >>= fun tm ->
      M.lift C.ask >>= fun psi ->
      M.lift @@ U.push_guess psi ~ty0:ty ~ty1:rst.ty tm

    | Tm.BoxModality ty, E.Shut e ->
      M.in_scope (Name.fresh ()) `Lock begin
        elab_chk env ty e
      end <<@> fun tm ->
        Tm.make @@ Tm.Shut tm

    | _, E.Hole name ->
      M.lift C.ask >>= fun psi ->
      M.lift @@ U.push_hole `Rigid psi ty >>= fun tm ->
      begin
        if name = Some "_" then M.ret () else
          M.emit e.span @@ M.UserHole {name; ty; tele = psi; tm = Tm.up tm}
      end >>
      M.ret @@ Tm.up tm

    | _, E.Hope ->
      M.lift C.ask >>= fun psi ->
      M.lift @@ U.push_hole `Flex psi ty <<@> Tm.up


    | _, E.Let info ->
      let itac =
        match info.ty with
        | None ->
          elab_inf env info.tm <<@> fun (let_ty, let_tm) ->
            let_ty, Tm.up let_tm
        | Some ety ->
          elab_chk env univ ety >>= fun let_ty ->
          elab_chk env let_ty info.tm <<@> fun let_tm ->
            let_ty, let_tm
      in
      let ctac ty = elab_chk env ty info.body in
      tac_let info.name itac ctac ty

    | Tm.Rst _, _ ->
      tac_rst (fun ty -> elab_chk env ty e) ty

    | _, E.Lam (names, e) ->
      let tac ty = elab_chk env ty e in
      tac_wrap_nf (tac_lambda names tac) ty

    | _, E.Quo tmfam ->
      get_resolver env >>= fun renv ->
      let tm = tmfam renv in
      begin
        match Tm.unleash tm with
        | Tm.Up _ ->
          elab_up env ty {e with con = E.Quo tmfam }
        | _ ->
          M.ret @@ tmfam renv
      end


    | _, E.Elim {mot; scrut; clauses} ->
      let tac_mot = Option.map (fun emot ty -> elab_chk env ty emot) mot in
      let tac_scrut = elab_inf env scrut <<@> fun (ty, cmd) -> ty, Tm.up cmd in
      let used = Hashtbl.create 10 in
      let elab_clause (lbl, pbinds, bdy) =
        if Hashtbl.mem used lbl then failwith "Duplicate clause in elimination" else
          begin
            Hashtbl.add used lbl ();
            lbl, pbinds, fun ty -> elab_chk env ty bdy
          end
      in
      let clauses = List.map elab_clause clauses in
      tac_elim ~loc:e.span ~tac_mot ~tac_scrut ~clauses ty

    | Tm.Univ _, E.Ext (names, ety, esys) ->
      let univ = ty in
      let xs = List.map (fun x -> Name.named (Some x)) names in
      let ps = List.map (fun x -> (x, `I)) xs in
      M.in_scopes ps begin
        elab_chk env univ ety >>= fun tyxs ->
        elab_tm_sys env tyxs esys <<@> fun sysxs ->
          let ebnd = Tm.bind_ext (Bwd.from_list xs) tyxs sysxs in
          let ext_ty = Tm.make @@ Tm.Ext ebnd in
          ext_ty
      end

    | Tm.Univ _, E.Rst (ety, esys) ->
      let univ = ty in
      elab_chk env univ ety >>= fun ty ->
      elab_tm_sys env ty esys <<@> fun sys ->
        Tm.make @@ Tm.Rst {ty; sys}

    | Tm.Univ _, E.Pi ([], e) ->
      elab_chk env ty e

    | Tm.Univ _, E.Pi (`Ty (name, edom) :: etele, ecod) ->
      elab_chk env ty edom >>= fun dom ->
      let x = Name.named @@ Some name in
      M.in_scope x (`P dom) begin
        elab_chk env ty {e with con = E.Pi (etele, ecod)}
        <<@> Tm.bind x
        <<@> fun cod -> Tm.make @@ Tm.Pi (dom, cod)
      end

    | Tm.Univ _, E.Pi (`I name :: etele, ecod) ->
      let x = Name.named @@ Some name in
      M.in_scope x `I begin
        elab_chk env ty { e with con = E.Pi (etele, ecod)}
        <<@> fun codx ->
          let ebnd = Tm.bind_ext (Emp #< x) codx [] in
          Tm.make @@ Tm.Ext ebnd
      end

    | Tm.Univ _, E.Pi (`Tick name :: etele, ecod) ->
      let x = Name.named @@ Some name in
      M.in_scope x `Tick begin
        elab_chk env ty {e with con = E.Pi (etele, ecod)}
        <<@> Tm.bind x
        <<@> fun bnd -> Tm.make @@ Tm.Later bnd
      end

    | Tm.Univ _, E.Pi (`Lock :: etele, ecod) ->
      let x = Name.fresh () in
      M.in_scope x `Lock begin
        elab_chk env ty {e with con = E.Pi (etele, ecod)}
        <<@> fun ty -> Tm.make @@ Tm.BoxModality ty
      end

    | Tm.Univ _, E.Sg ([], e) ->
      elab_chk env ty e

    | Tm.Univ _, E.Sg (`Ty (name, edom) :: etele, ecod) ->
      elab_chk env ty edom >>= fun dom ->
      let x = Name.named @@ Some name in
      M.in_scope x (`P dom) begin
        elab_chk env ty {e with con = E.Sg (etele, ecod)}
        <<@> Tm.bind x
        <<@> fun cod -> Tm.make @@ Tm.Sg (dom, cod)
      end


    | _, Tuple [] ->
      failwith "empty tuple"
    | _, Tuple [e] ->
      elab_chk env ty e
    | Tm.Sg (dom, cod), Tuple (e :: es) ->
      elab_chk env dom e >>= fun tm0 ->
      let cmd0 = Tm.ann ~ty:dom ~tm:tm0 in
      let cod' = Tm.make @@ Tm.Let (cmd0, cod) in
      elab_chk env cod' {e with con = E.Tuple es} <<@> Tm.cons tm0

    | Tm.Univ info, Type (kind, lvl) ->
      begin
        if Lvl.greater info.lvl lvl then
          match Tm.unleash ty with
          | Tm.Univ _ ->
            M.ret @@ Tm.univ ~kind ~lvl
          | _ ->
            failwith "Type"
        else
          failwith "Elaborator: universe level error"
      end

    | _, E.Cut (e, fs) ->
      elab_chk_cut env e fs ty

    | _, E.HCom info ->
      elab_dim env info.r >>= fun r ->
      elab_dim env info.r' >>= fun r' ->
      let kan_univ = Tm.univ ~lvl:`Omega ~kind:`Kan in
      begin
        M.lift @@ C.check ~ty:kan_univ ty >>= function
        | `Ok ->
          elab_chk env ty info.cap >>= fun cap ->
          elab_hcom_sys env r ty cap info.sys <<@> fun sys ->
            let hcom = Tm.HCom {r; r'; ty; cap; sys} in
            Tm.up (hcom, Emp)

        | `Exn exn ->
          raise exn
      end

    | _, E.Var _ ->
      elab_chk_cut env e Emp ty

    | _, _ ->
      elab_up env ty e

  and elab_tm_sys env ty =
    let rec go acc =
      function
      | [] ->
        M.ret @@ Bwd.to_list acc

      | (e_r, e_r', e) :: esys ->
        let rst_ty = Tm.make @@ Tm.Rst {ty; sys = Bwd.to_list acc} in
        elab_dim env e_r >>= fun r ->
        elab_dim env e_r' >>= fun r' ->
        begin
          M.under_restriction r r' begin
            elab_chk env rst_ty e
          end
        end >>= fun obnd ->
        let face = r, r', obnd in
        go (acc #< face) esys
    in
    go Emp

  and elab_hcom_sys env s ty cap =
    let rec go acc =
      function
      | [] ->
        M.ret @@ Bwd.to_list acc

      | (e_r, e_r', e) :: esys ->
        let x = Name.fresh () in
        let varx = Tm.up @@ Tm.var x in
        let ext_ty =
          let face_cap = varx, s, Some cap in
          let face_adj (r, r', obnd) =
            let bnd = Option.get_exn obnd in
            let tmx = Tm.unbind_with (Tm.var x) bnd in
            r, r', Some tmx
          in
          let faces_adj = List.map face_adj @@ Bwd.to_list acc in
          let faces = face_cap :: faces_adj in
          Tm.make @@ Tm.Ext (Tm.bind_ext (Emp #< x) ty faces)
        in
        elab_dim env e_r >>= fun r ->
        elab_dim env e_r' >>= fun r' ->
        begin
          M.under_restriction r r' begin
            elab_chk env ext_ty e >>= fun line ->
            M.in_scope x `I (M.lift @@ (ext_ty, line) %% Tm.ExtApp [varx]) >>= fun (_, tmx) ->
            M.ret @@ Tm.bind x tmx
          end
        end >>= fun obnd ->
        let face = r, r', obnd in
        go (acc #< face) esys

    in go Emp

  and elab_com_sys env s ty_bnd cap =
    let rec go acc =
      function
      | [] ->
        M.ret @@ Bwd.to_list acc

      | (e_r, e_r', e) :: esys ->
        let x = Name.fresh () in
        let varx = Tm.up @@ Tm.var x in
        let tyx = Tm.unbind_with (Tm.var x) ty_bnd in
        let ext_ty =
          let face_cap = varx, s, Some cap in
          let face_adj (r, r', obnd) =
            let bnd = Option.get_exn obnd in
            let tmx = Tm.unbind_with (Tm.var x) bnd in
            r, r', Some tmx
          in
          let faces_adj = List.map face_adj @@ Bwd.to_list acc in
          let faces = face_cap :: faces_adj in
          Tm.make @@ Tm.Ext (Tm.bind_ext (Emp #< x) tyx faces)
        in
        elab_dim env e_r >>= fun r ->
        elab_dim env e_r' >>= fun r' ->
        begin
          M.under_restriction r r' begin
            elab_chk env ext_ty e >>= fun line ->
            M.in_scope x `I (M.lift @@ (ext_ty, line) %% Tm.ExtApp [varx]) >>= fun (_, tmx) ->
            M.ret @@ Tm.bind x tmx
          end
        end >>= fun obnd ->
        let face = r, r', obnd in
        go (acc #< face) esys

    in go Emp

  and elab_up env ty inf =
    elab_inf env inf >>= fun (ty', cmd) ->
    M.lift (C.check_subtype ty' ty) >>= function
    | `Ok -> M.ret @@ Tm.up cmd
    | _ ->
      M.lift @@ C.active @@ Dev.Subtype {ty0 = ty'; ty1 = ty} >>
      M.unify >>
      M.lift (C.check_subtype ty' ty) >>= function
      | `Ok -> M.ret @@ Tm.up cmd
      | `Exn exn ->
        raise exn

  and elab_var env name ushift =
    get_resolver env <<@> fun renv ->
      begin
        match ResEnv.get name renv with
        | `Var a ->
          a, (Tm.Var {name = a; twin = `Only; ushift}, Emp)
        | _ ->
          failwith "elab_var: expected locally closed"
      end


  and elab_inf env e : (ty * tm Tm.cmd) M.m =
    match e.con with
    | E.Var (name, ushift) ->
      begin
        elab_var env name ushift >>= fun (a, cmd) ->
        M.lift (C.lookup_var a `Only) <+> (M.lift (C.lookup_meta a) <<@> fst) <<@> fun ty ->
          Tm.shift_univ ushift ty, cmd
      end <+>
      begin
        M.lift C.base_cx <<@> fun cx ->
          let sign = Cx.globals cx in
          let _ = GlobalEnv.lookup_datatype name sign in
          let univ0 = Tm.univ ~kind:`Kan ~lvl:(`Const 0) in
          univ0, Tm.ann ~ty:univ0 ~tm:(Tm.make @@ Tm.Data name)
      end

    | E.Quo tmfam ->
      get_resolver env >>= fun renv ->
      let tm = tmfam renv in
      begin
        match Tm.unleash tm with
        | Tm.Up cmd ->
          M.lift C.base_cx <<@> fun cx ->
            let vty = Typing.infer cx cmd in
            Cx.quote_ty cx vty, cmd
        | _ ->
          failwith "Cannot elaborate `term"
      end

    | E.Cut (e, fs) ->
      elab_cut env e fs

    | E.Coe info ->
      elab_dim env info.r >>= fun tr ->
      elab_dim env info.r' >>= fun tr' ->
      let x = Name.fresh () in
      let kan_univ = Tm.univ ~lvl:`Omega ~kind:`Kan in
      let univ_fam = Tm.make @@ Tm.Ext (Tm.bind_ext (Emp #< x) kan_univ []) in
      elab_chk env univ_fam info.fam >>= fun fam ->
      begin
        (M.lift @@ (univ_fam, fam) %% Tm.ExtApp [tr] <<@> snd)
        <&>
        (M.lift @@ (univ_fam, fam) %% Tm.ExtApp [tr'] <<@> snd)
      end >>= fun (fam_r, fam_r') ->
      elab_chk env fam_r info.tm <<@> fun tm ->
        let varx = Tm.up @@ Tm.var x in
        let tyx = Tm.up @@ Tm.ann ~ty:univ_fam ~tm:fam @< Tm.ExtApp [varx] in
        let coe = Tm.Coe {r = tr; r' = tr'; ty = Tm.bind x tyx; tm} in
        fam_r', (coe, Emp)

    | E.Com info ->
      elab_dim env info.r >>= fun tr ->
      elab_dim env info.r' >>= fun tr' ->
      let x = Name.fresh () in
      let kan_univ = Tm.univ ~lvl:`Omega ~kind:`Kan in
      let univ_fam = Tm.make @@ Tm.Ext (Tm.bind_ext (Emp #< x) kan_univ []) in
      elab_chk env univ_fam info.fam >>= fun fam ->
      M.lift @@ (univ_fam, fam) %% Tm.ExtApp [tr] >>= fun (_, fam_r) ->
      M.lift @@ (univ_fam, fam) %% Tm.ExtApp [tr'] >>= fun (_, fam_r') ->
      elab_chk env fam_r info.cap >>= fun cap ->
      M.in_scope x `I begin
        let varx = Tm.up @@ Tm.var x in
        M.lift @@ (univ_fam, fam) %% Tm.ExtApp [varx]
      end >>= fun (_, fam_x) ->
      let tybnd = Tm.bind x fam_x in
      elab_com_sys env tr tybnd cap info.sys <<@> fun sys ->
        let com = Tm.Com {r = tr; r' = tr'; ty = tybnd; cap; sys} in
        fam_r', (com, Emp)

    | E.DFixLine info ->
      elab_chk env univ info.ty >>= fun ty ->
      elab_dim env info.r >>= fun r ->
      let wk_ty = Tm.subst (Tm.shift 1) ty in
      let ltr_ty = Tm.make @@ Tm.Later (Tm.B (None, wk_ty)) in
      let x = Name.named @@ Some info.name in
      M.in_scope x (`P ltr_ty) begin
        elab_chk env ty info.bdy
        <<@> Tm.bind x
        <<@> fun bdy ->
          ltr_ty, (Tm.DFix {r; ty; bdy}, Emp)
      end

    | E.FixLine info ->
      elab_chk env univ info.ty >>= fun ty ->
      elab_dim env info.r >>= fun r ->
      let wk_ty = Tm.subst (Tm.shift 1) ty in
      let ltr_ty = Tm.make @@ Tm.Later (Tm.B (None, wk_ty)) in
      let x = Name.named @@ Some info.name in
      M.in_scope x (`P ltr_ty) begin
        elab_chk env ty info.bdy
        <<@> Tm.bind x
        <<@> fun bdy ->
          let dfix = Tm.DFix {r; ty; bdy}, Emp in
          let Tm.B (_, bdy') = bdy in
          let fix = Tm.subst (Tm.dot dfix @@ Tm.shift 0) bdy' in
          ty, Tm.ann ~tm:fix ~ty
      end

    | _ ->
      failwith "Can't infer"

  and elab_dim env e =
    match e.con with
    | E.Var (name, 0) ->
      get_resolver env >>= fun renv ->
      begin
        match ResEnv.get name renv with
        | `Var a ->
          M.ret @@ Tm.up @@ Tm.var a
        | `Ix _ ->
          failwith "elab_dim: expected locally closed"
      end
    | E.Num 0 ->
      M.ret @@ Tm.make Tm.Dim0
    | E.Num 1 ->
      M.ret @@ Tm.make Tm.Dim1
    | _ ->
      failwith "TODO: elab_dim"

  and bite_from_spine env spine =
    match spine with
    | Emp ->
      M.ret (spine, `Done)
    | Snoc (spine, frm) ->
      kind_of_frame env frm >>= function
      | `FunApp e ->
        M.ret (spine, `FunApp e)
      | `ExtApp dim ->
        bite_dims_from_spine env spine <<@> fun (spine, dims) ->
          spine, `ExtApp (Bwd.to_list @@ dims #< dim)
      | `Prev e ->
        M.ret (spine, `Prev e)
      | `Car ->
        M.ret (spine, `Car)
      | `Cdr ->
        M.ret (spine, `Cdr)
      | `Open ->
        M.ret (spine, `Open)

  and bite_dims_from_spine env spine =
    let rec go spine dims =
      match spine with
      | Emp ->
        M.ret (Emp, Bwd.from_list dims)
      | Snoc (spine, frm) ->
        kind_of_frame env frm >>= function
        | `ExtApp dim ->
          go spine @@ dim :: dims
        | _ ->
          M.ret (spine #< frm, Bwd.from_list dims)
    in
    go spine []


  and evaluator =
    M.lift C.base_cx <<@> fun cx ->
      cx, Cx.evaluator cx


  and elab_chk_cut env exp frms ty =
    match Tm.unleash ty with
    | Tm.Data dlbl ->
      begin
        match exp.con with
        | E.Var (clbl, _) ->
          begin
            M.lift C.base_cx >>= fun cx ->
            let sign = Cx.globals cx in
            let desc = GlobalEnv.lookup_datatype dlbl sign in
            let constr = Desc.lookup_constr clbl desc in
            elab_intro env dlbl clbl constr frms
          end
          <+> elab_mode_switch_cut env exp frms ty

        | _ ->
          elab_mode_switch_cut env exp frms ty
      end

    | _ ->
      elab_mode_switch_cut env exp frms ty

  and elab_intro env dlbl clbl constr frms =
    let rec go_const_args acc const_specs frms =
      match const_specs, frms with
      | [], _ ->
        M.ret (List.rev_map snd acc, frms)
      | (_, ty) :: const_specs, E.App e :: frms ->
        (* TODO: might be backwards *)
        let sub = List.fold_right (fun (ty,tm) sub -> Tm.dot (Tm.ann ~ty ~tm) sub) acc @@ Tm.shift 0 in
        let ty' = Tm.subst sub ty in
        elab_chk env ty' e >>= fun t ->
        go_const_args ((ty', t) :: acc) const_specs frms
      | _ ->
        failwith "elab_intro: malformed parameters"
    in
    let rec go_rec_args rec_specs dims frms =
      match rec_specs, dims, frms with
      | [], [], [] ->
        M.ret []
      | [], _ :: dims, E.App r :: frms ->
        (fun x xs -> x :: xs) <@>> elab_dim env r <*> go_rec_args rec_specs dims frms
      | (_, Desc.Self) :: rec_specs, dims, E.App e :: frms ->
        let self_ty = Tm.make @@ Tm.Data dlbl in
        (fun x xs -> x :: xs) <@>> elab_chk env self_ty e <*> go_rec_args rec_specs dims frms
      | _ ->
        failwith "todo: go_args"
    in
    go_const_args [] constr.const_specs @@ Bwd.to_list frms >>= fun (tps, frms) ->
    go_rec_args constr.rec_specs constr.dim_specs frms >>= fun targs ->
    M.ret @@ Tm.make @@ Tm.Intro (dlbl, clbl, tps @ targs)

  and elab_mode_switch_cut env exp frms ty =
    elab_cut env exp frms >>= fun (ty', cmd) ->
    M.lift @@ C.active @@ Dev.Subtype {ty0 = ty'; ty1 = ty} >>
    M.unify >>
    M.lift (C.check_subtype ty' ty) >>= function
    | `Ok ->
      M.ret @@ Tm.up cmd
    | `Exn exn ->
      raise exn

  and elab_cut env exp frms =
    elab_cut_ env exp frms >>= fun (ty, cmd) ->
    normalize_ty ty >>= fun ty ->
    M.ret (ty, cmd)

  and elab_cut_ env exp frms =
    let rec unleash tm =
      match Tm.unleash tm with
      | Tm.Rst rst -> unleash rst.ty
      | con -> con
    in

    let try_nf ty kont =
      try kont ty with
      | Refiner.ChkMatch ->
        normalize_ty ty >>= kont
    in


    bite_from_spine env frms >>= function
    | _, `Done ->
      elab_inf env exp

    | spine, `ExtApp dims ->
      let rec go dims (ty, cmd) =
        try_nf ty @@ fun ty ->
        match dims with
        | [] ->
          M.ret (ty, cmd)
        | _ ->
          match unleash ty with
          | Tm.Ext ebnd ->
            let Tm.NB (nms, _) = ebnd in
            let n = Bwd.length nms in
            let dims0, dims1 = ListUtil.split n dims in
            traverse (elab_dim env) dims0 >>= fun trs0 ->
            let ty, _ = Tm.unbind_ext_with (List.map (fun tr -> Tm.DownX tr, Emp) trs0) ebnd in
            go dims1 (ty, cmd @< (Tm.ExtApp trs0))
          | _ ->
            raise ChkMatch
      in
      elab_cut env exp spine >>= go dims

    | spine, `FunApp e ->
      elab_cut env exp spine >>= fun (ty, cmd) ->
      try_nf ty @@ fun ty ->
      begin
        match unleash ty with
        | Tm.Pi (dom, cod) ->
          elab_chk env dom e <<@> fun arg ->
            Tm.unbind_with (Tm.ann ~ty:dom ~tm:arg) cod, cmd @< Tm.FunApp arg
        | _ ->
          raise ChkMatch
      end

    | spine, `Car ->
      elab_cut env exp spine >>= fun (ty, cmd) ->
      try_nf ty @@ fun ty ->
      begin
        match unleash ty with
        | Tm.Sg (dom, _) ->
          M.ret (dom, cmd @< Tm.Car)
        | _ ->
          raise ChkMatch
      end


    | spine, `Cdr ->
      elab_cut env exp spine >>= fun (ty, cmd) ->
      try_nf ty @@ fun ty ->
      begin
        match unleash ty with
        | Tm.Sg (_dom, cod) ->
          let cod' = Tm.unbind_with (cmd @< Tm.Car) cod in
          M.ret (cod', cmd @< Tm.Cdr)
        | _ ->
          raise ChkMatch
      end

    | spine, `Prev {con = E.TickConst} ->
      M.in_scope (Name.fresh ()) `Lock begin
        elab_cut env exp spine
      end >>= fun (ty, cmd) ->
      try_nf ty @@ fun ty ->
      begin
        match unleash ty with
        | Later ltr ->
          let tick = Tm.make Tm.TickConst in
          let ty' = Tm.unbind_with (Tm.DownX tick, Emp) ltr in
          M.ret (ty', cmd @< Tm.Prev tick)
        | _ ->
          raise ChkMatch
      end

    | spine, `Prev {con = E.Var (name, _)} ->
      elab_var env name 0 >>= fun (_, tick) ->
      M.in_scope (Name.fresh ()) (`KillFromTick (Tm.up tick)) begin
        elab_cut env exp spine
      end >>= fun (ty, cmd) ->
      try_nf ty @@ fun ty ->
      begin
        match unleash ty with
        | Later ltr ->
          let ty' = Tm.unbind_with tick ltr in
          M.ret (ty', cmd @< Tm.Prev (Tm.up tick))
        | _ ->
          raise ChkMatch
      end

    | spine, `Open ->
      M.in_scope (Name.fresh ()) `ClearLocks begin
        elab_cut env exp spine
      end >>= fun (ty, cmd) ->
      try_nf ty @@ fun ty ->
      begin
        match unleash ty with
        | Tm.BoxModality ty' ->
          M.ret (ty', cmd @< Tm.Open)
        | _ ->
          raise ChkMatch
      end

    | _ ->
      failwith "elab_cut"


end

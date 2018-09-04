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

  open Dev

  module M = ElabMonad
  module MonadUtil = Monad.Util (M)
  module Notation = Monad.Notation (M)
  open Notation

  open Tm.Notation


  let traverse = MonadUtil.traverse

  let flip f x y = f y x

  module E = ESig
  module T = Map.Make (String)

  type elab_env = {names : Name.t T.t; desc_constrs : (Tm.NewDesc.constr * ty) T.t}
  let empty_elab_env = {names = T.empty; desc_constrs = T.empty}

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
      let renv = go_globals (ResEnv.init ()) @@ T.bindings env.names in
      go_locals renv psi

  let (<+>) m n =
    M.optional m >>= function
    | Some x -> M.ret x
    | None -> n


  let kind_of_frame env =
    function
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
                | (`P _ | `Tw _) -> M.ret @@ `FunApp e
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
      elab_chk env e {ty = cod; sys = []} >>= fun tm ->
      let alpha = Name.named @@ Some name in

      M.lift C.ask >>= fun psi ->
      M.lift @@ U.define psi alpha opacity cod tm >>= fun _ ->
      M.lift C.go_to_top >>
      M.unify <<@> fun _ ->
        let now1 = Unix.gettimeofday () in
        Format.printf "Defined %s (%fs).@." name (now1 -. now0);
        {env with names = T.add name alpha env.names}

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

    | E.Normalize e ->
      elab_inf env e >>= fun (ty, cmd) ->
      M.lift C.base_cx >>= fun cx ->
      let vty = Cx.eval cx ty in
      let el = Cx.eval_cmd cx cmd in
      let tm = Cx.quote cx ~ty:vty el in
      M.emit e.span @@ M.PrintTerm {ty = ty; tm} >>
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
    let univ = Tm.univ ~kind:`Pre ~lvl:`Omega in
    let open Desc in

    let rec go_params acc edesc : Tm.NewDesc.pdesc M.m =
      match edesc.params with
      | (nm, ety) :: params ->
        elab_chk env ety {ty = univ; sys = []} >>= fun ty ->
        let x = Name.named @@ Some nm in
        M.in_scope x (`P ty) @@ go_params (acc #< (Tm.up @@ Tm.var x)) {edesc with params} >>= fun tele ->
        M.ret @@ Tm.TCons (`Param ty, Tm.NewDesc.bind_pdesc x tele)

      | [] ->
        let params = Bwd.to_list acc in
        elab_constrs env Emp ~params edesc.constrs >>= fun constrs ->
        let desc = Tm.NewDesc.Desc {kind = edesc.kind; lvl = edesc.lvl; constrs} in
        M.ret @@ Tm.TNil desc

    and elab_constrs env acc ~params econstrs =
      match econstrs with
      | (clbl, econstr) :: econstrs ->
        elab_constr env ~params clbl econstr >>= fun constr ->
        let acc' = acc #< (clbl, constr) in
        let env' =
          {env with
           desc_constrs =
             let data_ty = Tm.make @@ Tm.Data {dlbl; params} in
             T.add clbl (constr, data_ty) env.desc_constrs }
        in
        elab_constrs env' acc' ~params econstrs
      | [] ->
        M.ret @@ Bwd.to_list acc


    and elab_constr env ~params clbl econstr =
      let rec go_const_specs econstr =
        match econstr.const_specs with
        | (nm, ety) :: const_specs ->
          elab_chk env ety {ty = univ; sys = []} >>= fun ty ->
          let x = Name.named @@ Some nm in
          M.in_scope x (`P ty) @@ go_const_specs {econstr with const_specs} >>= fun tele ->
          M.ret @@ Tm.TCons (`Const ty, Tm.NewDesc.bind_constr x tele)

        | [] ->
          go_rec_specs econstr >>= fun tele ->
          M.ret @@ Tm.TNil tele

      and go_rec_specs econstr =
        match econstr.rec_specs with
        | (nm, Desc.Self) :: rec_specs ->
          let x = Name.named @@ Some nm in
          M.in_scope x (`SelfArg Desc.Self) @@ go_rec_specs {econstr with rec_specs} >>= fun tele ->
          M.ret @@ Tm.TCons (`Rec, Tm.NewDesc.bind_rec_specs x tele)

        | [] ->
          go_dim_specs econstr >>= fun tele ->
          M.ret @@ Tm.TNil tele

      and go_dim_specs econstr =
        match econstr.dim_specs with
        | nm :: dim_specs ->
          let x = Name.named @@ Some nm in
          M.in_scope x `I @@ go_dim_specs {econstr with dim_specs} >>= fun tele ->
          M.ret @@ Tm.TCons (`I, Tm.NewDesc.bind_dim_specs x tele)

        | [] ->
          elab_boundary econstr >>= fun bsys ->
          M.ret @@ Tm.TNil bsys

      and elab_boundary econstr =
        let data_ty = Tm.make @@ Tm.Data {dlbl; params} in
        elab_tm_sys env data_ty econstr.boundary

      in
      go_const_specs econstr

    in
    go_params Emp edesc


  and elab_scheme env (cells, ecod) kont =
    let rec go =
      function
      | [] ->
        elab_chk env ecod {ty = univ; sys = []} >>=
        kont
      | `Ty (name, edom) :: cells ->
        elab_chk env edom {ty = univ; sys = []} >>= normalize_ty >>= fun dom ->
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
      | _ -> failwith "TODO: elab_scheme"
    in
    go cells



  (* TODO: we will be disentangling all the elaboration of concrete expressions from tactics which produce redtt proofs.
     As an example, see what we have done with tac_lambda, tac_if, etc. *)
  and elab_chk env e : chk_tac =
    fun goal ->
      (* TODO speed up elaboration by not normalizing, but raising ChkMatch if we don't know what to do.
         Then wrap the whole thing in tac_wrap_nf. *)
      normalize_ty goal.ty >>= fun ty ->
      let goal = {goal with ty} in
      match goal.sys, Tm.unleash ty, e.con with
      | _, _, E.Guess e ->
        tac_guess (elab_chk env e) goal

      | _, _, E.Hole name ->
        tac_hole ~loc:e.span ~name goal

      | _, _, E.Hope ->
        tac_hope goal

      | _, _, E.Refl ->
        tac_refl goal

      | _, _, E.Let info ->
        let itac =
          match info.ty with
          | None ->
            elab_inf env info.tm <<@> fun (let_ty, let_tm) ->
              let_ty, Tm.up let_tm
          | Some ety ->
            elab_chk env ety {ty = univ; sys = []} >>= fun let_ty ->
            elab_chk env info.tm {ty = let_ty; sys = []} <<@> fun let_tm ->
              let_ty, let_tm
        in
        let ctac goal = elab_chk env info.body goal in
        tac_let info.name itac ctac goal

      | _, _, E.Lam (names, e) ->
        let tac = elab_chk env e in
        tac_wrap_nf (tac_lambda names tac) goal

      | [], _, E.Quo tmfam ->
        get_resolver env >>= fun renv ->
        let tm = tmfam renv in
        begin
          match Tm.unleash tm with
          | Tm.Up _ ->
            elab_up env ty {e with con = E.Quo tmfam}
          | _ ->
            M.ret @@ tmfam renv
        end


      | [], _, E.Elim {mot; scrut; clauses} ->
        let tac_mot = Option.map (elab_chk env) mot in
        let tac_scrut = elab_inf env scrut <<@> fun (ty, cmd) -> ty, Tm.up cmd in
        let used = Hashtbl.create 10 in
        let elab_clause (lbl, pbinds, bdy) =
          if Hashtbl.mem used lbl then failwith "Duplicate clause in elimination" else
            begin
              Hashtbl.add used lbl ();
              lbl, pbinds, elab_chk env bdy
            end
        in
        let clauses = List.map elab_clause clauses in
        tac_elim ~loc:e.span ~tac_mot ~tac_scrut ~clauses goal

      | [], Tm.Univ _, E.Ext (names, ety, esys) ->
        let univ = ty in
        let xs = List.map (fun x -> Name.named (Some x)) names in
        let ps =
          match xs with
          | [] -> [(Name.fresh (), `NullaryExt)]
          | _ -> List.map (fun x -> (x, `I)) xs
        in
        M.in_scopes ps begin
          elab_chk env ety {ty = univ; sys = []} >>= fun tyxs ->
          elab_tm_sys env tyxs esys <<@> fun sysxs ->
            let ebnd = Tm.bind_ext (Bwd.from_list xs) tyxs sysxs in
            let ext_ty = Tm.make @@ Tm.Ext ebnd in
            ext_ty
        end

      | [], Tm.Univ _, E.Pi ([], e) ->
        elab_chk env e goal

      | [], Tm.Univ _, E.Pi (`Ty (name, edom) :: etele, ecod) ->
        elab_chk env edom {ty; sys = []} >>= fun dom ->
        let x = Name.named @@ Some name in
        M.in_scope x (`P dom) begin
          elab_chk env {e with con = E.Pi (etele, ecod)} {ty; sys = []}
          <<@> Tm.bind x
          <<@> fun cod -> Tm.make @@ Tm.Pi (dom, cod)
        end

      | [], Tm.Univ _, E.Pi (`I name :: etele, ecod) ->
        let x = Name.named @@ Some name in
        M.in_scope x `I begin
          elab_chk env { e with con = E.Pi (etele, ecod)} {ty; sys = []}
          <<@> fun codx ->
            let ebnd = Tm.bind_ext (Emp #< x) codx [] in
            Tm.make @@ Tm.Ext ebnd
        end

      | [], Tm.Univ _, E.Pi (`Tick name :: etele, ecod) ->
        let x = Name.named @@ Some name in
        M.in_scope x `Tick begin
          elab_chk env {e with con = E.Pi (etele, ecod)} {ty; sys = []}
          <<@> Tm.bind x
          <<@> fun bnd -> Tm.make @@ Tm.Later bnd
        end

      | [], Tm.Univ _, E.Sg ([], e) ->
        elab_chk env e {ty; sys = []}

      | [], Tm.Univ _, E.Sg (`Ty (name, edom) :: etele, ecod) ->
        elab_chk env edom {ty; sys = []} >>= fun dom ->
        let x = Name.named @@ Some name in
        M.in_scope x (`P dom) begin
          elab_chk env {e with con = E.Sg (etele, ecod)} {ty; sys = []}
          <<@> Tm.bind x
          <<@> fun cod -> Tm.make @@ Tm.Sg (dom, cod)
        end


      | _, _, Tuple [] ->
        failwith "empty tuple"

      | _, _, Tuple [e] ->
        elab_chk env e goal

      | _, Tm.Sg (dom, cod), Tuple (e0 :: es) as etuple ->
        let tac0 = elab_chk env e0 in
        let tac1 = elab_chk env @@ {e with con = Tuple es} in
        tac_pair tac0 tac1 goal

      | [], Tm.Univ info, Type (kind, lvl) ->
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

      | [], _, E.Cut (e, fs) ->
        elab_chk_cut env e fs ty

      | [], _, E.HCom info ->
        elab_dim env info.r >>= fun r ->
        elab_dim env info.r' >>= fun r' ->
        let kan_univ = Tm.univ ~lvl:`Omega ~kind:`Kan in
        begin
          M.lift @@ C.check ~ty:kan_univ ty >>= function
          | `Ok ->
            elab_chk env info.cap {ty; sys = []} >>= fun cap ->
            elab_hcom_sys env r ty cap info.sys <<@> fun sys ->
              let hcom = Tm.HCom {r; r'; ty; cap; sys} in
              Tm.up (hcom, Emp)

          | `Exn exn ->
            raise exn
        end

      | [], _, E.Var _ ->
        elab_chk_cut env e Emp ty

      | [], _, _ ->
        elab_up env ty e

      | _, _, _ ->
        elab_chk env e {goal with sys = []} >>= fun tm ->
        guess_restricted tm goal


  and elab_tm_sys env ty =
    let rec go acc =
      function
      | [] ->
        M.ret @@ Bwd.to_list acc

      | (e_r, e_r', e) :: esys ->
        elab_dim env e_r >>= fun r ->
        elab_dim env e_r' >>= fun r' ->
        begin
          M.under_restriction r r' begin
            elab_chk env e {ty; sys = Bwd.to_list acc}
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
            elab_chk env e {ty = ext_ty; sys = []} >>= fun line ->
            let tmx = Tm.up @@ Tm.ann ~ty:ext_ty ~tm:line @< Tm.ExtApp [varx] in
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
            elab_chk env e {ty = ext_ty; sys = []} >>= fun line ->
            let tmx = Tm.up @@ Tm.ann ~ty:ext_ty ~tm:line @< Tm.ExtApp [varx] in
            M.ret @@ Tm.bind x tmx
          end
        end >>= fun obnd ->
        let face = r, r', obnd in
        go (acc #< face) esys

    in go Emp

  and elab_up env ty inf =
    elab_inf env inf >>= fun (ty', cmd) ->
    M.lift (C.check ~ty @@ Tm.up cmd) >>= function
    | `Ok -> M.ret @@ Tm.up cmd
    | `Exn exn ->
      M.lift @@ C.active @@ Dev.Subtype {ty0 = ty'; ty1 = ty} >>
      M.unify >>
      M.lift (C.check ~ty @@ Tm.up cmd) >>= function
      | `Ok ->
        M.ret @@ Tm.up cmd
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
      elab_chk env info.fam {ty = univ_fam; sys = []} >>= fun fam ->

      let fam_cmd = Tm.ann ~ty:univ_fam ~tm:fam in
      let fam_r = Tm.up @@ fam_cmd @< Tm.ExtApp [tr] in
      let fam_r' = Tm.up @@ fam_cmd @< Tm.ExtApp [tr'] in
      elab_chk env info.tm {ty = fam_r; sys = []} <<@> fun tm ->
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
      elab_chk env info.fam {ty = univ_fam; sys = []} >>= fun fam ->

      let fam_cmd = Tm.ann ~ty:univ_fam ~tm:fam in
      let fam_r = Tm.up @@ fam_cmd @< Tm.ExtApp [tr] in
      let fam_r' = Tm.up @@ fam_cmd @< Tm.ExtApp [tr'] in

      elab_chk env info.cap {ty = fam_r; sys = []} >>= fun cap ->

      let varx = Tm.up @@ Tm.var x in
      let fam_x = Tm.up @@ fam_cmd @< Tm.ExtApp [varx] in
      let tybnd = Tm.bind x fam_x in
      elab_com_sys env tr tybnd cap info.sys <<@> fun sys ->
        let com = Tm.Com {r = tr; r' = tr'; ty = tybnd; cap; sys} in
        fam_r', (com, Emp)

    | E.DFixLine info ->
      elab_chk env info.ty {ty = univ; sys = []} >>= fun ty ->
      elab_dim env info.r >>= fun r ->
      let wk_ty = Tm.subst (Tm.shift 1) ty in
      let ltr_ty = Tm.make @@ Tm.Later (Tm.B (None, wk_ty)) in
      let x = Name.named @@ Some info.name in
      M.in_scope x (`P ltr_ty) begin
        elab_chk env info.bdy {ty; sys = []}
        <<@> Tm.bind x
        <<@> fun bdy ->
          ltr_ty, (Tm.DFix {r; ty; bdy}, Emp)
      end

    | E.FixLine info ->
      elab_chk env info.ty {ty = univ; sys = []} >>= fun ty ->
      elab_dim env info.r >>= fun r ->
      let wk_ty = Tm.subst (Tm.shift 1) ty in
      let ltr_ty = Tm.make @@ Tm.Later (Tm.B (None, wk_ty)) in
      let x = Name.named @@ Some info.name in
      M.in_scope x (`P ltr_ty) begin
        elab_chk env info.bdy {ty; sys = []}
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
    | Tm.Data data ->
      begin
        match exp.con with
        | E.Var (clbl, _) ->
          elab_mode_switch_cut env exp frms ty
          <+>
          begin
            elab_intro env data.dlbl data.params clbl frms
          end

        | _ ->
          elab_mode_switch_cut env exp frms ty
      end

    | Tm.Univ _ ->
      begin
        match exp.con with
        | E.Var (dlbl, _) ->
          begin
            M.lift C.base_cx >>= fun cx ->
            let sign = Cx.globals cx in
            let desc = GlobalEnv.lookup_datatype dlbl sign in
            elab_data env dlbl desc frms
          end
          <+> elab_mode_switch_cut env exp frms ty
        | _ ->
          elab_mode_switch_cut env exp frms ty
      end

    | _ ->
      elab_mode_switch_cut env exp frms ty


  and lookup_constr env dlbl params clbl =
    M.lift C.base_cx >>= fun cx ->
    let sign = Cx.globals cx in
    match GlobalEnv.lookup_datatype dlbl sign with
    | pdesc ->
      let Tm.NewDesc.Desc {constrs} = Tm.NewDesc.inst_pdesc pdesc params in
      let _, constr =
        flip List.find constrs @@ fun (clbl', _) ->
        clbl' = clbl
      in
      M.ret constr
    | exception _ ->
      let constr, _ = T.find clbl env.desc_constrs in
      M.ret constr


  and elab_intro env dlbl params clbl frms =
    lookup_constr env dlbl params clbl >>= fun constr ->

    let rec go_const_args sb (tele : Tm.NewDesc.constr) frms =
      match tele, frms with
      | Tm.TNil tele, _ ->
        go_rec_args sb tele frms

      | Tm.TCons (`Const ty, Tm.B (_, tele)), E.App e :: frms ->
        let ty = Tm.subst sb ty in
        elab_chk env e {ty; sys = []} >>= fun tm ->
        let sb' = Tm.dot (Tm.ann ~ty ~tm) sb in
        go_const_args sb' tele frms >>= fun args ->
        M.ret @@ tm :: args

      | _ ->
        failwith "Unexpected frame in constant arguments of constructor"

    and go_rec_args sb tele frms =
      match tele, frms with
      | Tm.TNil tele, _ ->
        go_dim_args sb tele frms

      | Tm.TCons (`Rec, Tm.B (_, tele)), E.App e :: frms ->
        let ty = Tm.make @@ Tm.Data {dlbl; params} in
        elab_chk env e {ty; sys = []} >>= fun tm ->
        let sb' = Tm.dot (Tm.ann ~ty ~tm) sb in
        go_rec_args sb' tele frms >>= fun args ->
        M.ret @@ tm :: args

      | _ ->
        failwith "Unexpected frame in recursive arguments of constructor"

    and go_dim_args sb tele frms =
      match tele, frms with
      | Tm.TNil _, [] ->
        M.ret []

      | Tm.TCons (`I, Tm.B (_, tele)), E.App e :: frms ->
        elab_dim env e >>= fun tr ->
        let sb' = Tm.dot (Tm.DownX tr, Emp) sb in
        go_dim_args sb' tele frms >>= fun args ->
        M.ret @@ tr :: args

      | _ ->
        failwith "Unexpected frame in dimension arguments of constructor"

    in
    go_const_args (Tm.shift 0) constr @@ Bwd.to_list frms >>= fun args ->
    M.ret @@ Tm.make @@ Tm.Intro (dlbl, clbl, args)

  and elab_data env dlbl pdesc frms =
    let rec go sb tele frms =
      match pdesc, frms with
      | Tm.TNil _, [] ->
        M.ret []

      | Tm.TCons (`Param ty, Tm.B (_, tele)), E.App e :: frms ->
        let ty = Tm.subst sb ty in
        elab_chk env e {ty; sys = []} >>= fun tm ->
        let sb' = Tm.dot (Tm.ann ~ty ~tm) sb in
        go sb' tele frms

      | _ ->
        failwith "Unexpected frame in parameters of datatype"

    in
    go (Tm.shift 0) pdesc @@ Bwd.to_list frms >>= fun params ->
    M.ret @@ Tm.make @@ Tm.Data {dlbl; params}

  and elab_mode_switch_cut env exp frms ty =
    elab_cut env exp frms >>= fun (ty', cmd) ->
    M.lift (C.check ~ty @@ Tm.up cmd) >>= function
    | `Ok ->
      M.ret @@ Tm.up cmd
    | `Exn exn ->
      M.lift @@ C.active @@ Dev.Subtype {ty0 = ty'; ty1 = ty} >>
      M.unify >>
      M.lift (C.check ~ty @@ Tm.up cmd) >>= function
      | `Ok ->
        M.ret @@ Tm.up cmd
      | `Exn exn ->
        M.lift @@ C.dump_state Format.err_formatter "foo" `All >>= fun _ ->
        Format.eprintf "raising exn@.";
        raise exn

  and elab_cut env exp frms =
    elab_cut_ env exp frms >>= fun (ty, cmd) ->
    normalize_ty ty >>= fun ty ->
    M.ret (ty, cmd)

  and elab_cut_ env exp frms =
    let rec unleash tm =
      match Tm.unleash tm with
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
          elab_chk env e {ty = dom; sys = []} <<@> fun arg ->
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

    | _ ->
      failwith "elab_cut"


end

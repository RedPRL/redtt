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

  open Refiner

  type mode =
    | Chk of ty
    | Inf

  let univ = Tm.univ ~lvl:`Omega ~kind:`Pre

  let (<+>) m n =
    M.optional m >>= function
    | Some x -> M.ret x
    | None -> n


  let kind_of_frame =
    function
    | E.App ({con = E.Num (0 | 1)} as e) ->
      M.ret @@ `ExtApp e
    | E.App ({con = E.Var {name = nm; _}} as e) ->
      M.lift @@ C.resolver >>= fun renv ->
      begin
        try
          begin
            match ResEnv.get nm renv with
            | `Var alpha ->
              M.lift C.get_global_env >>= fun env ->
              begin
                match GlobalEnv.lookup env alpha with
                | (`P _ | `Tw _ | `Def _) -> M.ret @@ `FunApp e
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



  let rec elab_sig =
    function
    | [] ->
      M.ret ()
    | E.Debug f :: esig ->
      elab_decl @@ E.Debug f >>= fun _ ->
      elab_sig esig
    | E.Quit :: _ ->
      M.ret ()
    | dcl :: esig ->
      elab_decl dcl >>= fun _ ->
      elab_sig esig


  and elab_decl =
    function
    | E.Define (name, opacity, scheme, e) ->
      let now0 = Unix.gettimeofday () in
      elab_scheme scheme >>= fun (names, ty) ->
      let xs = List.map (fun nm -> Name.named @@ Some nm) names in
      let bdy_tac = tac_wrap_nf @@ tac_lambda xs @@ elab_chk e in
      bdy_tac {ty; sys = []} >>= fun tm ->
      let alpha = Name.named @@ Some name in
      M.lift @@ U.define Emp alpha opacity ty tm >>= fun _ ->
      M.lift C.go_to_top >>
      M.unify <<@> fun _ ->
        let now1 = Unix.gettimeofday () in
        Format.printf "Defined %s (%fs).@." name (now1 -. now0)

    | E.Data (dlbl, edesc) ->
      elab_datatype dlbl edesc >>= fun desc ->
      M.lift @@ C.declare_datatype dlbl desc

    | E.Debug filter ->
      let title =
        match filter with
        | `All -> "Development state:"
        | `Constraints -> "Unsolved constraints:"
        | `Unsolved -> "Unsolved entries:"
      in
      M.lift @@ C.dump_state Format.std_formatter title filter

    | E.Normalize e ->
      elab_inf e >>= fun (ty, cmd) ->
      M.lift C.base_cx >>= fun cx ->
      let vty = Cx.eval cx ty in
      let el = Cx.eval_cmd cx cmd in
      let tm = Cx.quote cx ~ty:vty el in
      M.emit e.span @@ M.PrintTerm {ty = ty; tm}


    | E.Import file_name ->
      begin
        match I.import file_name with
        | `Cached ->
          M.ret ()
        | `Elab esig ->
          elab_sig esig
      end

    | E.Quit ->
      M.ret ()

  and elab_datatype dlbl edesc =
    let rec go tdesc =
      function
      | [] ->
        let tdesc = Desc.{tdesc with status = `Complete} in
        M.lift @@ C.declare_datatype dlbl tdesc >>
        M.ret tdesc
      | econstr :: econstrs ->
        elab_constr dlbl tdesc econstr >>= fun constr ->
        let tdesc = Desc.{tdesc with constrs = tdesc.constrs @ [constr]} in
        M.lift @@ C.declare_datatype dlbl tdesc >>
        go tdesc econstrs
    in

    let tdesc = Desc.{edesc with constrs = []; status = `Partial} in
    M.lift @@ C.declare_datatype dlbl tdesc >>= fun _ ->
    match edesc.kind with
    | `Reg ->
      failwith "elab_datatype: Not yet sure what conditions need to be checked for `Reg kind"
    | _ ->
      go tdesc edesc.constrs

  and elab_constr dlbl desc (clbl, constr) =
    if List.exists (fun (lbl, _) -> clbl = lbl) desc.constrs then
      failwith "Duplicate constructor in datatype";

    let data_ty = Tm.make @@ Tm.Data dlbl in

    let open Desc in
    let elab_rec_spec (x, Self) = M.ret (x, Self) in

    let rec abstract_tele xs (ps : _ list) =
      match ps with
      | [] -> []
      | (lbl, x, p) :: ps ->
        let Tm.NB (_, p') = Tm.bindn xs p in
        (lbl, p') :: abstract_tele (xs #< x) ps
    in

    let rec go acc =
      function
      | [] ->
        let const_specs = abstract_tele Emp @@ Bwd.to_list acc in
        (* TODO: when self args are more complex, we'll need to abstract them over
           the parameters too. *)
        traverse elab_rec_spec constr.rec_specs >>= fun rec_specs ->


        let psi =
          List.map (fun (nm, ty) -> (Name.named @@ Some nm, `P data_ty)) rec_specs
          @ List.map (fun nm -> (Name.named @@ Some nm, `I)) constr.dim_specs
        in
        M.in_scopes psi @@
        begin
          elab_constr_boundary dlbl desc (const_specs, rec_specs, constr.dim_specs) constr.boundary >>= fun boundary ->
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
        elab_chk ety {ty = univ; sys = []} >>= bind_in_scope >>= fun pty ->
        let x = Name.named @@ Some lbl in
        M.in_scope x (`P pty) @@
        go (acc #< (lbl, x, pty)) const_specs
    in

    go Emp constr.const_specs

  and elab_constr_boundary dlbl desc (const_specs, rec_specs, dim_specs) sys : (Tm.tm, Tm.tm) Tm.system M.m =
    M.lift C.base_cx >>= fun cx ->
    let (module V) = Cx.evaluator cx in
    let module D = Domain in

    let rec build_cx cx env const_specs rec_specs dim_specs =
      match const_specs, rec_specs, dim_specs with
      | (plbl, pty) :: const_specs, _, _ ->
        let vty = V.eval env pty in
        let cx', v = Cx.ext_ty cx ~nm:(Some plbl) vty in
        build_cx cx' (D.Env.snoc env @@ `Val v)  const_specs rec_specs dim_specs
      | [], (nm, Desc.Self) :: rec_specs, _ ->
        let cx_x, _ = Cx.ext_ty cx ~nm:(Some nm) @@ D.make @@ D.Data dlbl in
        build_cx cx_x env  const_specs rec_specs dim_specs
      | [], [], nm :: dim_specs ->
        let cx', _ = Cx.ext_dim cx ~nm:(Some nm) in
        build_cx cx' env  const_specs rec_specs dim_specs
      | [], [], [] ->
        cx
    in

    let cx' = build_cx cx V.empty_env const_specs rec_specs dim_specs in
    traverse (elab_constr_face dlbl desc) sys >>= fun bdry ->
    let data_ty = D.make @@ D.Data dlbl in
    Typing.check_tm_sys cx' data_ty bdry;
    M.ret bdry

  and elab_constr_face dlbl desc (er0, er1, e) =
    let e = Option.get_exn e in
    elab_dim er0 >>= fun r0 ->
    bind_in_scope r0 >>= fun r0' ->
    elab_dim er1 >>= fun r1 ->
    bind_in_scope r1 >>= fun r1' ->
    M.in_scope (Name.fresh ()) (`R (r0, r1)) @@
    begin
      elab_boundary_term dlbl desc e <<@> fun bt ->
        r0', r1', Some bt
    end

  and elab_boundary_term dlbl desc e =
    match e.con with
    | E.Var {name = nm; _} ->
      elab_boundary_cut dlbl desc nm Emp
    | E.Cut ({con = E.Var {name = nm; _}}, spine) ->
      elab_boundary_cut dlbl desc nm spine
    | _ ->
      failwith "TODO: elaborate_boundary_term"

  and boundary_resolve_name desc name =
    let open Desc in
    begin
      M.lift C.resolver >>= fun renv ->
      match ResEnv.get name renv with
      | `Var x ->
        M.lift C.ask >>= fun psi ->
        let go (x, param) =
          match param with
          | `P _ -> [x]
          | `Def _ -> [x]
          | `I -> [x]
          | `Tick -> [x]
          | `Tw _ -> []
          | _ -> []
        in
        let xs = Bwd.flat_map go psi in
        let ix = Bwd.length xs - 1 - (ListUtil.index_of (fun y -> x = y) @@ Bwd.to_list xs) in
        M.ret @@ `Ix ix
      | _ ->
        failwith "impossible"
    end
    <+>
    begin
      M.ret () >>= fun _ ->
      M.ret @@ `Constr (List.find (fun (lbl, _) -> name = lbl) desc.constrs)
    end

  and elab_boundary_cut dlbl desc name spine =
    boundary_resolve_name desc name >>= function
    | `Ix ix ->
      begin
        match spine with
        | Emp ->
          M.ret @@ Tm.up @@ Tm.ix ix
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
          elab_chk e {ty = pty'; sys = []} >>= bind_in_scope >>= fun t ->
          go_const_specs ((pty', t) :: acc) ps frms
        | _ ->
          failwith "elab_intro: malformed parameters"
      in

      let rec go_args acc rec_specs frms =
        match rec_specs, frms with
        | [], _ ->
          M.ret (Bwd.to_list acc, frms)
        | (_, Desc.Self) :: rec_specs, E.App e :: frms ->
          elab_boundary_term dlbl desc e >>= fun bt ->
          go_args (acc #< bt) rec_specs frms
        | _ ->
          failwith "todo: go_args"
      in

      let rec go_dims acc dim_specs frms =
        match dim_specs, frms with
        | [], [] ->
          M.ret @@ Bwd.to_list acc
        | _ :: dim_specs, E.App e :: frms ->
          elab_dim e >>= bind_in_scope >>= fun r ->
          go_dims (acc #< r) dim_specs frms
        | _ ->
          failwith "Dimensions length mismatch in boundary term"
      in

      go_const_specs [] constr.const_specs @@ Bwd.to_list spine >>= fun (const_args, frms) ->
      go_args Emp constr.rec_specs frms >>= fun (rec_args, frms) ->
      go_dims Emp constr.dim_specs frms >>= fun rs ->
      M.ret @@ Tm.make @@ Tm.Intro (dlbl, clbl, const_args @ rec_args @ rs)




  and elab_scheme (sch : E.escheme) : (string list * Tm.tm) M.m =
    let cells, ecod = sch in
    let rec go =
      function
      | [] ->
        elab_chk ecod {ty = univ; sys = []}
      | `Ty (name, edom) :: cells ->
        elab_chk edom {ty = univ; sys = []} >>= normalize_ty >>= fun dom ->
        let x = Name.named @@ Some name in
        M.in_scope x (`P dom) (go cells) <<@> fun codx ->
          Tm.make @@ Tm.Pi (dom, Tm.bind x codx)
      | `Tick name :: cells ->
        let x = Name.named @@ Some name in
        M.in_scope x `Tick (go cells) <<@> fun tyx ->
          Tm.make @@ Tm.Later (Tm.bind x tyx)
      | `I name :: cells ->
        let x = Name.named @@ Some name in
        M.in_scope x `I (go cells) <<@> fun tyx ->
          Tm.make @@ Tm.Ext (Tm.bind_ext (Emp #< x) tyx [])
    in

    let name_of_cell = function `I nm | `Tick nm | `Ty (nm, _) -> nm in
    let names = List.map name_of_cell cells in

    go cells <<@> fun ty ->
      names, ty


  (* TODO: we will be disentangling all the elaboration of concrete expressions from tactics which produce redtt proofs.
     As an example, see what we have done with tac_lambda, tac_if, etc. *)
  and elab_chk e : chk_tac =
    fun goal ->
      (* TODO speed up elaboration by not normalizing, but raising ChkMatch if we don't know what to do.
         Then wrap the whole thing in tac_wrap_nf. *)
      normalize_ty goal.ty >>= fun ty ->
      let goal = {goal with ty} in
      match goal.sys, Tm.unleash ty, e.con with
      | _, _, E.Guess e ->
        tac_guess (elab_chk e) goal

      | _, _, E.Hole (name, None) ->
        tac_hole ~loc:e.span ~name goal

      | _, _, E.Hole (name, Some e') ->
        inspect_goal ~loc:e.span ~name goal >>
        elab_chk e' goal

      | _, _, E.Hope ->
        tac_hope goal

      | _, _, E.Refl ->
        tac_refl goal

      | _, _, E.Let info ->
        elab_scheme info.sch >>= fun (names, pity) ->
        let ctac goal = elab_chk info.tm goal in
        let xs = List.map (fun nm -> Name.named @@ Some nm) names in
        let lambdas = tac_wrap_nf (tac_lambda xs ctac) in
        let inf_tac = lambdas {ty = pity; sys = []} <<@> fun ltm -> pity, ltm in
        let body_tac = elab_chk info.body in
        tac_let (Name.named @@ Some info.name) inf_tac body_tac goal

      | _, _, E.Lam (names, e) ->
        let tac = elab_chk e in
        let xs = List.map (fun nm -> Name.named @@ Some nm) names in
        tac_wrap_nf (tac_lambda xs tac) goal

      | [], _, E.Quo tmfam ->
        M.lift C.resolver >>= fun renv ->
        let tm = tmfam renv in
        begin
          match Tm.unleash tm with
          | Tm.Up _ ->
            elab_up ty {e with con = E.Quo tmfam}
          | _ ->
            M.ret @@ tmfam renv
        end


      | [], _, E.Elim {mot; scrut; clauses} ->
        let tac_mot = Option.map elab_chk mot in
        let tac_scrut = elab_inf scrut <<@> fun (ty, cmd) -> ty, Tm.up cmd in
        let used = Hashtbl.create 10 in
        let elab_clause (lbl, pbinds, bdy) =
          if Hashtbl.mem used lbl then failwith "Duplicate clause in elimination" else
            begin
              Hashtbl.add used lbl ();
              lbl, pbinds, elab_chk bdy
            end
        in
        let clauses = List.map elab_clause clauses in
        tac_elim ~loc:e.span ~tac_mot ~tac_scrut ~clauses goal

      | [], Tm.Pi (dom, _), E.ElimFun {clauses} ->
        let x = Name.fresh () in
        let tac_mot = None in
        let tac_scrut = M.ret (dom, Tm.up @@ Tm.var x) in
        let used = Hashtbl.create 10 in
        let elab_clause (lbl, pbinds, bdy) =
          if Hashtbl.mem used lbl then failwith "Duplicate clause in elimination" else
            begin
              Hashtbl.add used lbl ();
              lbl, pbinds, elab_chk bdy
            end
        in
        let clauses = List.map elab_clause clauses in
        let tac_fun =
          tac_lambda [x] @@
          tac_elim ~loc:e.span ~tac_mot:None ~tac_scrut ~clauses
        in
        tac_fun goal

      | [], Tm.Univ _, E.Ext (names, ety, esys) ->
        let univ = ty in
        let xs = List.map (fun x -> Name.named (Some x)) names in
        let ps =
          match xs with
          | [] -> [(Name.fresh (), `NullaryExt)]
          | _ -> List.map (fun x -> (x, `I)) xs
        in
        M.in_scopes ps begin
          elab_chk ety {ty = univ; sys = []} >>= fun tyxs ->
          elab_tm_sys tyxs esys <<@> fun sysxs ->
            let ebnd = Tm.bind_ext (Bwd.from_list xs) tyxs sysxs in
            let ext_ty = Tm.make @@ Tm.Ext ebnd in
            ext_ty
        end

      | [], Tm.Univ _, E.Pi ([], e) ->
        elab_chk e goal

      | [], Tm.Univ _, E.Pi (`Ty (name, edom) :: etele, ecod) ->
        elab_chk edom {ty; sys = []} >>= fun dom ->
        let x = Name.named @@ Some name in
        M.in_scope x (`P dom) begin
          elab_chk {e with con = E.Pi (etele, ecod)} {ty; sys = []}
          <<@> Tm.bind x
          <<@> fun cod -> Tm.make @@ Tm.Pi (dom, cod)
        end

      | [], Tm.Univ _, E.Pi (`I name :: etele, ecod) ->
        let x = Name.named @@ Some name in
        M.in_scope x `I begin
          elab_chk { e with con = E.Pi (etele, ecod)} {ty; sys = []}
          <<@> fun codx ->
            let ebnd = Tm.bind_ext (Emp #< x) codx [] in
            Tm.make @@ Tm.Ext ebnd
        end

      | [], Tm.Univ _, E.Pi (`Tick name :: etele, ecod) ->
        let x = Name.named @@ Some name in
        M.in_scope x `Tick begin
          elab_chk {e with con = E.Pi (etele, ecod)} {ty; sys = []}
          <<@> Tm.bind x
          <<@> fun bnd -> Tm.make @@ Tm.Later bnd
        end

      | [], Tm.Univ _, E.Sg ([], e) ->
        elab_chk e {ty; sys = []}

      | [], Tm.Univ _, E.Sg (`Ty (name, edom) :: etele, ecod) ->
        elab_chk edom {ty; sys = []} >>= fun dom ->
        let x = Name.named @@ Some name in
        M.in_scope x (`P dom) begin
          elab_chk {e with con = E.Sg (etele, ecod)} {ty; sys = []}
          <<@> Tm.bind x
          <<@> fun cod -> Tm.make @@ Tm.Sg (dom, cod)
        end


      | _, _, Tuple [] ->
        failwith "empty tuple"

      | _, _, Tuple [e] ->
        elab_chk e goal

      | _, Tm.Sg (dom, cod), Tuple (e0 :: es) as etuple ->
        let tac0 = elab_chk e0 in
        let tac1 = elab_chk @@ {e with con = Tuple es} in
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
        elab_chk_cut e fs ty

      | [], _, E.HCom info ->
        elab_dim info.r >>= fun r ->
        elab_dim info.r' >>= fun r' ->
        let kan_univ = Tm.univ ~lvl:`Omega ~kind:`Kan in
        begin
          M.lift @@ C.check ~ty:kan_univ ty >>= function
          | `Ok ->
            elab_chk info.cap {ty; sys = []} >>= fun cap ->
            elab_hcom_sys r ty cap info.sys <<@> fun sys ->
              let hcom = Tm.HCom {r; r'; ty; cap; sys} in
              Tm.up (hcom, Emp)

          | `Exn exn ->
            raise exn
        end

      | [], _, E.Var _ ->
        elab_chk_cut e Emp ty

      | [], _, _ ->
        elab_up ty e

      | _, _, _ ->
        elab_chk e {goal with sys = []} >>= fun tm ->
        guess_restricted tm goal


  and elab_tm_sys ty =
    let rec go acc =
      function
      | [] ->
        M.ret @@ Bwd.to_list acc

      | (xis, e) :: esys ->
        go_face acc esys e xis

    and go_face acc esys e =
      function
      | [] ->
        go acc esys
      | (e_r, e_r') :: xis ->
        elab_dim e_r >>= fun r ->
        elab_dim e_r' >>= fun r' ->
        begin
          M.under_restriction r r' begin
            elab_chk e {ty; sys = Bwd.to_list acc}
          end
        end >>= fun obnd ->
        let face = r, r', obnd in
        go_face (acc #< face) esys e xis
    in
    go Emp



  and elab_hcom_sys s ty cap =
    let rec go acc =
      function
      | [] ->
        M.ret @@ Bwd.to_list acc

      | (xis, e) :: esys ->
        go_face acc esys e xis

    and go_face acc esys e =
      function
      | [] ->
        go acc esys
      | (e_r, e_r') :: xis ->
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
        elab_dim e_r >>= fun r ->
        elab_dim e_r' >>= fun r' ->
        begin
          M.under_restriction r r' begin
            elab_chk e {ty = ext_ty; sys = []} >>= fun line ->
            let tmx = Tm.up @@ Tm.ann ~ty:ext_ty ~tm:line @< Tm.ExtApp [varx] in
            M.ret @@ Tm.bind x tmx
          end
        end >>= fun obnd ->
        let face = r, r', obnd in
        go_face (acc #< face) esys e xis

    in go Emp

  and elab_com_sys s ty_bnd cap =
    let rec go acc =
      function
      | [] ->
        M.ret @@ Bwd.to_list acc

      | (xis, e) :: esys ->
        go_face acc esys e xis

    and go_face acc esys e =
      function
      | [] ->
        go acc esys
      | (e_r, e_r') :: xis ->
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
        elab_dim e_r >>= fun r ->
        elab_dim e_r' >>= fun r' ->
        begin
          M.under_restriction r r' begin
            elab_chk e {ty = ext_ty; sys = []} >>= fun line ->
            let tmx = Tm.up @@ Tm.ann ~ty:ext_ty ~tm:line @< Tm.ExtApp [varx] in
            M.ret @@ Tm.bind x tmx
          end
        end >>= fun obnd ->
        let face = r, r', obnd in
        go_face (acc #< face) esys e xis

    in go Emp

  and elab_up ty inf =
    elab_inf inf >>= fun (ty', cmd) ->
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

  and elab_var name ushift =
    M.lift C.resolver <<@> fun renv ->
      begin
        match ResEnv.get name renv with
        | `Var a ->
          a, (Tm.Var {name = a; twin = `Only; ushift}, Emp)
        | _ ->
          failwith "elab_var: expected locally closed"
      end


  and elab_inf e : (ty * tm Tm.cmd) M.m =
    match e.con with
    | E.Var {name; ushift} ->
      M.lift C.resolver >>= fun renv ->
      begin
        match ResEnv.get name renv with
        | `Var x ->
          M.lift (C.lookup_var x `Only) <<@> fun ty ->
            Tm.shift_univ ushift ty, (Tm.Var {name = x; twin = `Only; ushift}, Emp)

        | `Metavar x ->
          M.lift (C.lookup_meta x) <<@> fun (ty, _) ->
            Tm.shift_univ ushift ty, (Tm.Meta {name = x; ushift}, Emp)


        | `Datatype dlbl ->
          M.lift C.base_cx <<@> fun cx ->
            let sign = Cx.globals cx in
            let _ = GlobalEnv.lookup_datatype name sign in
            let univ0 = Tm.univ ~kind:`Kan ~lvl:(`Const 0) in
            univ0, Tm.ann ~ty:univ0 ~tm:(Tm.make @@ Tm.Data name)

        | `Ix _ ->
          failwith "elab_inf: impossible"
      end

    | E.Quo tmfam ->
      M.lift C.resolver >>= fun renv ->
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
      elab_cut e fs

    | E.Coe info ->
      elab_dim info.r >>= fun tr ->
      elab_dim info.r' >>= fun tr' ->
      let x = Name.fresh () in
      let kan_univ = Tm.univ ~lvl:`Omega ~kind:`Kan in
      let univ_fam = Tm.make @@ Tm.Ext (Tm.bind_ext (Emp #< x) kan_univ []) in
      elab_chk info.fam {ty = univ_fam; sys = []} >>= fun fam ->

      let fam_cmd = Tm.ann ~ty:univ_fam ~tm:fam in
      let fam_r = Tm.up @@ fam_cmd @< Tm.ExtApp [tr] in
      let fam_r' = Tm.up @@ fam_cmd @< Tm.ExtApp [tr'] in
      elab_chk info.tm {ty = fam_r; sys = []} <<@> fun tm ->
        let varx = Tm.up @@ Tm.var x in
        let tyx = Tm.up @@ Tm.ann ~ty:univ_fam ~tm:fam @< Tm.ExtApp [varx] in
        let coe = Tm.Coe {r = tr; r' = tr'; ty = Tm.bind x tyx; tm} in
        fam_r', (coe, Emp)

    | E.Com info ->
      elab_dim info.r >>= fun tr ->
      elab_dim info.r' >>= fun tr' ->
      let x = Name.fresh () in
      let kan_univ = Tm.univ ~lvl:`Omega ~kind:`Kan in
      let univ_fam = Tm.make @@ Tm.Ext (Tm.bind_ext (Emp #< x) kan_univ []) in
      elab_chk info.fam {ty = univ_fam; sys = []} >>= fun fam ->

      let fam_cmd = Tm.ann ~ty:univ_fam ~tm:fam in
      let fam_r = Tm.up @@ fam_cmd @< Tm.ExtApp [tr] in
      let fam_r' = Tm.up @@ fam_cmd @< Tm.ExtApp [tr'] in

      elab_chk info.cap {ty = fam_r; sys = []} >>= fun cap ->

      let varx = Tm.up @@ Tm.var x in
      let fam_x = Tm.up @@ fam_cmd @< Tm.ExtApp [varx] in
      let tybnd = Tm.bind x fam_x in
      elab_com_sys tr tybnd cap info.sys <<@> fun sys ->
        let com = Tm.Com {r = tr; r' = tr'; ty = tybnd; cap; sys} in
        fam_r', (com, Emp)

    | E.DFixLine info ->
      elab_chk info.ty {ty = univ; sys = []} >>= fun ty ->
      elab_dim info.r >>= fun r ->
      let wk_ty = Tm.subst (Tm.shift 1) ty in
      let ltr_ty = Tm.make @@ Tm.Later (Tm.B (None, wk_ty)) in
      let x = Name.named @@ Some info.name in
      M.in_scope x (`P ltr_ty) begin
        elab_chk info.bdy {ty; sys = []}
        <<@> Tm.bind x
        <<@> fun bdy ->
          ltr_ty, (Tm.DFix {r; ty; bdy}, Emp)
      end

    | E.FixLine info ->
      elab_chk info.ty {ty = univ; sys = []} >>= fun ty ->
      elab_dim info.r >>= fun r ->
      let wk_ty = Tm.subst (Tm.shift 1) ty in
      let ltr_ty = Tm.make @@ Tm.Later (Tm.B (None, wk_ty)) in
      let x = Name.named @@ Some info.name in
      M.in_scope x (`P ltr_ty) begin
        elab_chk info.bdy {ty; sys = []}
        <<@> Tm.bind x
        <<@> fun bdy ->
          let dfix = Tm.DFix {r; ty; bdy}, Emp in
          let Tm.B (_, bdy') = bdy in
          let fix = Tm.subst (Tm.dot dfix @@ Tm.shift 0) bdy' in
          ty, Tm.ann ~tm:fix ~ty
      end

    | _ ->
      failwith "Can't infer"

  and elab_dim e =
    match e.con with
    | E.Var {name; ushift = 0} ->
      M.lift C.resolver >>= fun renv ->
      begin
        match ResEnv.get name renv with
        | `Var a ->
          M.ret @@ Tm.up @@ Tm.var a
        | _ ->
          failwith "elab_dim: expected locally closed"
      end
    | E.Num 0 ->
      M.ret @@ Tm.make Tm.Dim0
    | E.Num 1 ->
      M.ret @@ Tm.make Tm.Dim1
    | _ ->
      failwith "TODO: elab_dim"

  and bite_from_spine spine =
    match spine with
    | Emp ->
      M.ret (spine, `Done)
    | Snoc (spine, frm) ->
      kind_of_frame frm >>= function
      | `FunApp e ->
        M.ret (spine, `FunApp e)
      | `ExtApp dim ->
        bite_dims_from_spine spine <<@> fun (spine, dims) ->
          spine, `ExtApp (Bwd.to_list @@ dims #< dim)
      | `Prev e ->
        M.ret (spine, `Prev e)
      | `Car ->
        M.ret (spine, `Car)
      | `Cdr ->
        M.ret (spine, `Cdr)
      | `Open ->
        M.ret (spine, `Open)

  and bite_dims_from_spine spine =
    let rec go spine dims =
      match spine with
      | Emp ->
        M.ret (Emp, Bwd.from_list dims)
      | Snoc (spine, frm) ->
        kind_of_frame frm >>= function
        | `ExtApp dim ->
          go spine @@ dim :: dims
        | _ ->
          M.ret (spine #< frm, Bwd.from_list dims)
    in
    go spine []


  and evaluator =
    M.lift C.base_cx <<@> fun cx ->
      cx, Cx.evaluator cx


  and elab_chk_cut exp frms ty =
    match Tm.unleash ty with
    | Tm.Data dlbl ->
      begin
        match exp.con with
        | E.Var {name = clbl; _} ->
          begin
            M.lift C.base_cx >>= fun cx ->
            let sign = Cx.globals cx in
            let desc = GlobalEnv.lookup_datatype dlbl sign in
            let constr = Desc.lookup_constr clbl desc in
            elab_intro dlbl clbl constr frms
          end
          <+> elab_mode_switch_cut exp frms ty

        | _ ->
          elab_mode_switch_cut exp frms ty
      end

    | _ ->
      elab_mode_switch_cut exp frms ty

  and elab_intro dlbl clbl constr frms =
    let rec go_const_args acc const_specs frms =
      match const_specs, frms with
      | [], _ ->
        M.ret (List.rev_map snd acc, frms)
      | (_, ty) :: const_specs, E.App e :: frms ->
        (* TODO: might be backwards *)
        let sub = List.fold_right (fun (ty,tm) sub -> Tm.dot (Tm.ann ~ty ~tm) sub) acc @@ Tm.shift 0 in
        let ty' = Tm.subst sub ty in
        elab_chk e {ty = ty'; sys = []} >>= fun t ->
        go_const_args ((ty', t) :: acc) const_specs frms
      | _ ->
        failwith "elab_intro: malformed parameters"
    in
    let rec go_rec_args rec_specs dims frms =
      match rec_specs, dims, frms with
      | [], [], [] ->
        M.ret []
      | [], _ :: dims, E.App r :: frms ->
        (fun x xs -> x :: xs) <@>> elab_dim r <*> go_rec_args rec_specs dims frms
      | (_, Desc.Self) :: rec_specs, dims, E.App e :: frms ->
        let self_ty = Tm.make @@ Tm.Data dlbl in
        (fun x xs -> x :: xs) <@>> elab_chk e {ty = self_ty; sys = []} <*> go_rec_args rec_specs dims frms
      | _ ->
        failwith "todo: go_args"
    in
    go_const_args [] constr.const_specs @@ Bwd.to_list frms >>= fun (tps, frms) ->
    go_rec_args constr.rec_specs constr.dim_specs frms >>= fun targs ->
    M.ret @@ Tm.make @@ Tm.Intro (dlbl, clbl, tps @ targs)

  and elab_mode_switch_cut exp frms ty =
    elab_cut exp frms >>= fun (ty', cmd) ->
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

  and elab_cut exp frms =
    elab_cut_ exp frms >>= fun (ty, cmd) ->
    normalize_ty ty >>= fun ty ->
    M.ret (ty, cmd)

  and elab_cut_ exp frms =
    let rec unleash tm =
      match Tm.unleash tm with
      | con -> con
    in

    let try_nf ty kont =
      try kont ty with
      | Refiner.ChkMatch ->
        normalize_ty ty >>= kont
    in


    bite_from_spine frms >>= function
    | _, `Done ->
      elab_inf exp

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
            traverse elab_dim dims0 >>= fun trs0 ->
            let ty, _ = Tm.unbind_ext_with (List.map (fun tr -> Tm.DownX tr, Emp) trs0) ebnd in
            go dims1 (ty, cmd @< (Tm.ExtApp trs0))
          | _ ->
            raise ChkMatch
      in
      elab_cut exp spine >>= go dims

    | spine, `FunApp e ->
      elab_cut exp spine >>= fun (ty, cmd) ->
      try_nf ty @@ fun ty ->
      begin
        match unleash ty with
        | Tm.Pi (dom, cod) ->
          elab_chk e {ty = dom; sys = []} <<@> fun arg ->
            Tm.unbind_with (Tm.ann ~ty:dom ~tm:arg) cod, cmd @< Tm.FunApp arg
        | _ ->
          raise ChkMatch
      end

    | spine, `Car ->
      elab_cut exp spine >>= fun (ty, cmd) ->
      try_nf ty @@ fun ty ->
      begin
        match unleash ty with
        | Tm.Sg (dom, _) ->
          M.ret (dom, cmd @< Tm.Car)
        | _ ->
          raise ChkMatch
      end


    | spine, `Cdr ->
      elab_cut exp spine >>= fun (ty, cmd) ->
      try_nf ty @@ fun ty ->
      begin
        match unleash ty with
        | Tm.Sg (_dom, cod) ->
          let cod' = Tm.unbind_with (cmd @< Tm.Car) cod in
          M.ret (cod', cmd @< Tm.Cdr)
        | _ ->
          raise ChkMatch
      end

    | spine, `Prev {con = E.Var {name; _}} ->
      elab_var name 0 >>= fun (_, tick) ->
      M.in_scope (Name.fresh ()) (`KillFromTick (Tm.up tick)) begin
        elab_cut exp spine
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

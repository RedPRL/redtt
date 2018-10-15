(* Experimental code *)
open RedTT_Core
open RedBasis
open Bwd open BwdNotation
open Combinators

module type Import =
sig
  val import : per_process : Contextual.per_process -> mlconf : ML.mlconf -> selector : string list
    -> [`New of ResEnv.t * Contextual.per_process | `Cached of ResEnv.t]
end

module type S =
sig
  val eval_cmd : ML.mlcmd -> ML.semcmd Contextual.m 
end

module Make (I : Import) : S =
struct

  module C = Contextual
  module U = Unify

  open Dev

  module M = C
  module MonadUtil = Monad.Util (M)
  module Notation = Monad.Notation (M)
  open Notation

  open Tm.Notation


  let traverse = MonadUtil.traverse

  module E = ML

  open Refiner

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
      C.resolver >>= fun renv ->
      begin
        try
          begin
            match ResEnv.get nm renv with
            | `Var alpha ->
              C.get_global_env >>= fun env ->
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
    | E.Fst ->
      M.ret `Fst
    | E.Snd ->
      M.ret `Snd
    | E.Open ->
      M.ret `Open

  let with_mlenv f k =
    C.get_mlenv >>= fun env0 ->
    C.modify_mlenv f >>
    k >>= fun x ->
    C.modify_mlenv (fun _ -> env0) >>
    M.ret x


  let rec eval_cmd =
    function
    | E.MlRet v -> eval_val v <<@> fun v -> E.SemRet v

    | E.MlBind (cmd0, x, cmd1) ->
      eval_cmd cmd0 <<@> unleash_ret >>= fun v0 ->
      C.modify_mlenv (E.Env.set x v0) >>
      eval_cmd cmd1

    | E.MlUnleash v ->
      begin
        eval_val v >>= function
        | E.SemThunk (env, cmd) ->
          with_mlenv (fun _ -> env) @@ eval_cmd cmd
        | _ ->
          failwith "eval_cmd: expected thunk"
      end

    | E.MlLam (x, c) ->
      C.get_mlenv <<@> fun env ->
        E.SemClo (env, x, c)

    | E.MlApp (c, v) ->
      begin
        eval_val v >>= fun v ->
        eval_cmd c >>= function
        | E.SemClo (env, x, c) ->
          with_mlenv (fun _ -> E.Env.set x v env) @@ eval_cmd c
        | E.SemElabClo (env, e) ->
          begin
            match v with
            | E.SemTuple [E.SemTerm ty; E.SemSys sys] ->
              with_mlenv (fun _ -> env) @@
              elab_chk e {ty; sys} >>= fun tm ->
              M.ret @@ E.SemRet (E.SemTerm tm)
            | _ ->
              failwith "MlApp of ElabClo: calling convention violated"
          end
        | _ ->
          failwith "expected ml closure"
      end

    | E.MlElab e ->
      C.get_mlenv >>= fun env ->
      M.ret @@ E.SemElabClo (env, e)

    | E.MlElabWithScheme (scheme, e) ->
      elab_scheme scheme >>= fun (names, ty) ->
      let xs = List.map (fun nm -> `Var (`Gen (Name.named @@ Some nm))) names in
      let bdy_tac = tac_wrap_nf @@ tac_lambda xs @@ elab_chk e in
      bdy_tac {ty; sys = []} >>= fun tm ->
      M.ret @@ E.SemRet (E.SemTuple [E.SemTerm ty; E.SemTerm tm])

    | MlCheck {ty; tm} ->
      eval_val ty <<@> E.unleash_term >>= fun ty ->
      eval_val tm <<@> E.unleash_term >>= fun tm ->
      begin
        C.check ~ty tm >>= function
        | `Ok ->
          M.ret @@ E.SemRet (E.SemTerm (Tm.up @@ Tm.ann ~ty ~tm))
        | `Exn exn ->
          raise exn
      end

    | E.MlDefine info ->
      begin
        eval_val info.tm <<@> E.unleash_term >>= fun tm ->
        eval_val info.ty <<@> E.unleash_term >>= fun ty ->
        eval_val info.name <<@> E.unleash_ref >>= fun alpha ->
        U.define Emp alpha info.visibility info.opacity ty tm >>= fun _ ->
        M.ret @@ E.SemRet (E.SemTuple [])
      end

    | E.MlDeclData info ->
      elab_datatype info.visibility info.name info.desc >>= fun desc ->
      C.replace_datatype info.name desc >>
      M.ret @@ E.SemRet (E.SemDataDesc desc)

    | E.MlImport (visibility, selector) ->
      C.get_per_process >>= fun per_process ->
      C.get_mlenv <<@> E.Env.get_mlconf >>= fun mlconf ->
      begin
        match I.import ~per_process ~mlconf ~selector with
        | `Cached res -> C.ret res
        | `New (res, per_process) ->
          C.set_per_process per_process >> C.ret res
      end >>= fun res ->
      C.modify_top_resolver (ResEnv.import_globals ~visibility res) >>
      M.ret @@ E.SemRet (E.SemTuple [])

    | E.MlUnify ->
      C.go_to_top >>
      Refiner.unify >>
      M.ret @@ E.SemRet (E.SemTuple [])

    | E.MlNormalize v ->
      eval_val v >>= fun v ->
      begin
        match v with
        | E.SemTuple [E.SemTerm ty; E.SemTerm tm] ->
          C.base_cx >>= fun cx ->
          let vty = Cx.eval cx ty in
          let el = Cx.eval cx tm in
          let tm = Cx.quote cx ~ty:vty el in
          M.ret @@ E.SemRet (E.SemTerm tm)
        | _ ->
          failwith "normalize: expected synthesizable term"
      end

    | E.MlSplit (tuple, xs, cmd) ->
      begin
        eval_val tuple >>= function
        | E.SemTuple vs ->
          C.modify_mlenv (List.fold_right2 E.Env.set xs vs) >>
          eval_cmd cmd
        | _ ->
          failwith "expected tuple"
      end

    | E.MlPrint info ->
      eval_val info.con >>= fun v ->
      let pp fmt () = ML.pp_semval fmt v in
      Log.pp_message ~loc:info.span ~lvl:`Info pp Format.std_formatter ();
      M.ret @@ E.SemRet (E.SemTuple [])

    | E.MlForeign (foreign, input) ->
      eval_val input <<@> foreign >>= eval_cmd

    | E.MlDebug filter ->
      M.dump_state Format.std_formatter "Debug" filter >>
      M.ret @@ E.SemRet (E.SemTuple [])

    | E.MlGetConf ->
      C.get_mlenv <<@> E.Env.get_mlconf <<@> fun mlconf -> E.SemRet (E.SemConf mlconf)

  and unleash_ret =
    function
    | E.SemRet v -> v
    | _ -> failwith "unleash_ret"

  and eval_val =
    function
    | E.MlDataDesc desc -> M.ret @@ E.SemDataDesc desc
    | E.MlTerm tm -> M.ret @@ E.SemTerm tm
    | E.MlSys tm -> M.ret @@ E.SemSys tm
    | E.MlVar x -> C.get_mlenv <<@> fun env -> Option.get_exn @@ E.Env.find x env
    | E.MlTuple vs -> traverse eval_val vs <<@> fun rs -> E.SemTuple rs
    | E.MlThunk mlcmd -> C.get_mlenv <<@> fun env -> E.SemThunk (env, mlcmd)
    | E.MlRef nm -> M.ret @@ E.SemRef nm
    | E.MlString str -> M.ret @@ E.SemString str
    | E.MlFloat x -> M.ret @@ E.SemFloat x
    | E.MlConf x -> M.ret @@ E.SemConf x

  and elab_datatype visibility dlbl (E.EDesc edesc) =
    let rec elab_params : _ -> (_ * Desc.body) M.m =
      function
      | [] ->
        M.ret ([], Desc.TNil [])
      | `Ty (name, edom) :: cells ->
        elab_chk edom {ty = univ; sys = []} >>= normalize_ty >>= fun ty ->
        let x = Name.named @@ Some name in
        M.in_scope x (`P ty) (elab_params cells) <<@> fun (psi, rest) ->
          (x, `P ty) :: psi, Desc.TCons (ty, Desc.Body.bind x rest)
      | _ ->
        failwith "elab_params"
    in

    let rec elab_constrs params tdesc =
      function
      | [] ->
        let tdesc = Desc.{tdesc with status = `Complete} in
        C.replace_datatype dlbl tdesc >>
        M.ret tdesc
      | econstr :: econstrs ->
        elab_constr dlbl params tdesc econstr >>= fun constr ->
        let tdesc = Desc.add_constr tdesc constr in
        C.replace_datatype dlbl tdesc >>
        elab_constrs params tdesc econstrs
    in

    elab_params edesc.params >>= fun (psi, tbody) ->
    M.in_scopes psi @@
    let tdesc = Desc.{body = tbody; status = `Partial; kind = edesc.kind; lvl = edesc.lvl} in
    C.declare_datatype visibility dlbl tdesc >>= fun _ ->
    match edesc.kind with
    | `Reg ->
      failwith "elab_datatype: Not yet sure what conditions need to be checked for `Reg kind"
    | _ ->
      elab_constrs psi tdesc edesc.constrs

  and elab_constr dlbl psi desc (clbl, E.EConstr econstr) =
    if List.exists (fun (lbl, _) -> clbl = lbl) @@ Desc.constrs desc then
      failwith "Duplicate constructor in datatype";

    let params = List.map (fun (x, _) -> Tm.up @@ Tm.var x) psi in
    let data_ty = Tm.make @@ Tm.Data {lbl = dlbl; params} in

    let elab_rec_spec (x, Desc.Self) = M.ret (x, Desc.Self) in

    let rec go =
      function
      | [] ->
        elab_tm_sys data_ty econstr.boundary <<@> fun boundary ->
          Desc.TNil boundary

      | `Ty (nm, ety) :: args ->
        begin
          match E.(ety.con) with
          | E.Var var when var.name = dlbl ->
            let x = Name.named @@ Some nm in
            M.in_scope x (`P data_ty) (go args) <<@> fun constr ->
              Desc.TCons (`Rec Desc.Self, Desc.Constr.bind x constr)
          | _ ->
            let x = Name.named @@ Some nm in
            let univ = Tm.univ ~kind:desc.kind ~lvl:desc.lvl in
            elab_chk ety {ty = univ; sys = []} >>= fun pty ->
            C.check ~ty:univ pty >>= function
            | `Ok ->
              M.in_scope x (`P pty) (go args) <<@> fun constr ->
                Desc.TCons (`Const pty, Desc.Constr.bind x constr)
            | `Exn exn ->
              raise exn
        end

      | `I nm :: args ->
        let x = Name.named @@ Some nm in
        M.in_scope x `I (go args) <<@> fun constr ->
          Desc.TCons (`Dim, Desc.Constr.bind x constr)

      | `Tick _ :: args ->
        failwith "Tick in HIT constructor argument not yet supported"

    in

    let rec rebind_constr n psi constr =
      match psi with
      | Emp -> constr
      | Snoc (psi, (x, _)) ->
        rebind_constr (n + 1) psi @@
        Desc.Constr.close_var x n constr
    in

    go econstr.specs <<@> fun constr ->
      clbl, rebind_constr 0 (Bwd.from_list psi) constr


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
      | _, _, E.RunML c ->
        let mlgoal = E.MlTuple [E.MlTerm ty; E.MlSys goal.sys] in
        let script = E.MlApp (c, mlgoal) in
        begin
          eval_cmd script <<@> unleash_ret >>= function
          | E.SemTerm tm -> M.ret tm
          | _ -> failwith "error running ML tactic"
        end

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
        let ps = List.map (fun nm -> `Var (`Gen (Name.named @@ Some nm))) names in
        let lambdas = tac_wrap_nf (tac_lambda ps ctac) in
        let inf_tac = lambdas {ty = pity; sys = []} <<@> fun ltm -> pity, ltm in
        let body_tac = elab_chk info.body in
        begin
          match info.pat, names with
          | `Var nm, _ ->
            tac_let (name_of nm) inf_tac body_tac goal
          | pat, [] ->
            tac_inv_let pat inf_tac body_tac goal
          | _ ->
            failwith "Unsupported destructuring let-binding"
        end

      | _, _, E.Lam (ps, e) ->
        let tac = elab_chk e in
        tac_wrap_nf (tac_lambda ps tac) goal

      | [], _, E.Quo tmfam ->
        C.resolver >>= fun renv ->
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
        let clauses, default = elab_elim_clauses clauses in
        tac_elim ~loc:e.span ~tac_mot ~tac_scrut ~clauses ~default goal

      | [], Tm.Pi (dom, _), E.ElimFun {clauses} ->
        let x = Name.fresh () in
        let tac_mot = None in
        let tac_scrut = M.ret (dom, Tm.up @@ Tm.var x) in
        let clauses, default = elab_elim_clauses clauses in
        let tac_fun =
          tac_lambda [`Var (`Gen x)] @@
          tac_elim ~loc:e.span ~tac_mot:None ~tac_scrut ~clauses ~default
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
          C.check ~ty:kan_univ ty >>= function
          | `Ok ->
            elab_chk info.cap {ty; sys = []} >>= fun cap ->
            elab_hcom_sys r ty cap info.sys <<@> fun sys ->
              let hcom = Tm.HCom {r; r'; ty; cap; sys} in
              Tm.up (hcom, [])

          | `Exn exn ->
            raise exn
        end

      | [], _, E.Var _ ->
        elab_chk_cut e [] ty

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


  and elab_elim_clauses clauses =
    let used = Hashtbl.create 10 in
    let tac_clauses =
      flip ListUtil.filter_map clauses @@ function
      | `Con (lbl, pbinds, bdy) ->
        if Hashtbl.mem used lbl then failwith "Duplicate clause in elimination" else
          begin
            Hashtbl.add used lbl ();
            Some (lbl, pbinds, elab_chk bdy)
          end
      | `All bdy ->
        None
    in
    let tac_default =
      flip ListUtil.find_map_opt clauses @@ function
      | `All bdy -> Some (elab_chk bdy)
      | _ -> None
    in

    tac_clauses, tac_default

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
    C.check ~ty @@ Tm.up cmd >>= function
    | `Ok -> M.ret @@ Tm.up cmd
    | `Exn exn ->
      C.active @@ Dev.Subtype {ty0 = ty'; ty1 = ty} >>
      unify >>
      C.check ~ty @@ Tm.up cmd >>= function
      | `Ok ->
        M.ret @@ Tm.up cmd
      | `Exn exn ->
        raise exn

  and elab_var name ushift =
    C.resolver <<@> fun renv ->
      begin
        match ResEnv.get name renv with
        | `Var a ->
          a, (Tm.Var {name = a; twin = `Only; ushift}, [])
        | _ ->
          failwith "elab_var: expected locally closed"
      end


  and elab_inf e : (ty * tm Tm.cmd) M.m =
    match e.con with
    | E.Var {name; ushift} ->
      C.resolver >>= fun renv ->
      begin
        match ResEnv.get name renv with
        | `Var x ->
          C.lookup_var x `Only <<@> fun ty ->
            Tm.shift_univ ushift ty, (Tm.Var {name = x; twin = `Only; ushift}, [])

        | `Metavar x ->
          C.lookup_meta x <<@> fun (ty, _) ->
            Tm.shift_univ ushift ty, (Tm.Meta {name = x; ushift}, [])

        | _ ->
          failwith "elab_inf: impossible"
      end

    | E.Quo tmfam ->
      C.resolver >>= fun renv ->
      let tm = tmfam renv in
      begin
        match Tm.unleash tm with
        | Tm.Up cmd ->
          C.base_cx <<@> fun cx ->
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
        fam_r', (coe, [])

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
        fam_r', (com, [])

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
          ltr_ty, (Tm.DFix {r; ty; bdy}, [])
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
          let dfix = Tm.DFix {r; ty; bdy}, [] in
          let Tm.B (_, bdy') = bdy in
          let fix = Tm.subst (Tm.dot dfix @@ Tm.shift 0) bdy' in
          ty, Tm.ann ~tm:fix ~ty
      end

    | E.Elim {mot = Some mot; scrut; clauses} ->
      let tac_mot = elab_chk mot in
      let tac_scrut = elab_inf scrut <<@> fun (ty, cmd) -> ty, Tm.up cmd in
      let clauses, default = elab_elim_clauses clauses in
      tac_elim_inf ~loc:e.span ~tac_mot ~tac_scrut ~clauses ~default <<@> fun (ty, tm) ->
        ty, Tm.ann ~ty ~tm

    | _ ->
      Format.eprintf "Elaborator error: %a@." ML.pp e.con;
      failwith "Can't infer"

  and elab_dim e =
    match e.con with
    | E.Var {name; ushift = 0} ->
      C.resolver >>= fun renv ->
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
      | `Fst ->
        M.ret (spine, `Fst)
      | `Snd ->
        M.ret (spine, `Snd)
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
    C.base_cx <<@> fun cx ->
      cx, Cx.evaluator cx


  and elab_chk_cut exp frms ty =
    match Tm.unleash ty with
    | Tm.Data data ->
      let dlbl = data.lbl in
      begin
        match exp.con with
        | E.Var {name; _} ->
          C.base_cx >>= fun cx ->
          let sign = Cx.globals cx in
          begin
            match GlobalEnv.lookup_datatype dlbl sign with
            | desc ->
              let constrs = Desc.Body.instance data.params desc.body in
              begin
                match Desc.lookup_constr name constrs with
                | constr ->
                  elab_intro dlbl data.params name constr frms
                | exception _ ->
                  elab_mode_switch_cut exp frms ty
              end

            | exception _ ->
              elab_mode_switch_cut exp frms ty
          end

        | _ ->
          elab_mode_switch_cut exp frms ty
      end

    | _ ->
      match exp.con with
      | E.Var {name; _} ->
        C.resolver >>= fun renv ->
        begin
          match ResEnv.get name renv with
          | `Datatype dlbl ->
            elab_data dlbl frms
          | _ ->
            elab_mode_switch_cut exp frms ty
        end
      | _ ->
        elab_mode_switch_cut exp frms ty


  and elab_data dlbl frms =
    C.base_cx >>= fun cx ->
    let sign = Cx.globals cx in
    let desc = GlobalEnv.lookup_datatype dlbl sign in

    let rec go acc tele frms =
      match tele, frms with
      | Desc.TNil _, [] ->
        let params = Bwd.to_list acc in
        M.ret @@ Tm.make @@ Tm.Data {lbl = dlbl; params}

      | Desc.TCons (pty, btele), E.App e :: frms ->
        elab_chk e {ty = pty; sys = []} >>= fun tm ->
        let tele = Desc.Body.unbind_with (Tm.ann ~ty:pty ~tm:tm) btele in
        go (acc #< tm) tele frms

      | _ ->
        failwith "elab_data: length mismatch"

    in
    go Emp desc.body frms


  and realize_rspec ~dlbl ~params =
    function
    | Desc.Self ->
      Tm.make @@ Tm.Data {lbl = dlbl; params}

  and elab_intro dlbl params clbl constr frms =
    let elab_arg sub spec frm =
      match spec, frm with
      | `Const ty, E.App e ->
        let ty = Tm.subst sub ty in
        elab_chk e {ty; sys = []} >>= fun tm ->
        let sub = Tm.dot (Tm.ann ~ty ~tm) sub in
        M.ret (sub, tm)

      | `Rec rspec, E.App e ->
        let ty = realize_rspec ~dlbl ~params rspec in
        elab_chk e {ty; sys = []} >>= fun tm ->
        let sub = Tm.dot (Tm.ann ~ty ~tm) sub in
        M.ret (sub, tm)

      | `Dim, E.App e ->
        elab_dim e >>= fun r ->
        let sub = Tm.dot (Tm.DownX r, []) sub in
        M.ret (sub, r)

      | _ ->
        failwith "elab_intro: unexpected frame"
    in

    let rec go sub specs frms =
      match specs, frms with
      | (_, spec) :: specs, frm :: frms ->
        elab_arg sub spec frm >>= fun (sub, tm) ->
        go sub specs frms >>= fun tms ->
        M.ret (tm :: tms)

      | [], [] ->
        M.ret []

      | _ ->
        failwith "elab_intro: mismatch"
    in

    go (Tm.shift 0) (Desc.Constr.specs constr) frms >>= fun tms ->
    M.ret @@ Tm.make @@ Tm.Intro (dlbl, clbl, params, tms)

  and elab_mode_switch_cut exp frms ty =
    elab_cut exp frms >>= fun (ty', cmd) ->
    C.check ~ty @@ Tm.up cmd >>= function
    | `Ok ->
      M.ret @@ Tm.up cmd
    | `Exn exn ->
      C.active @@ Dev.Subtype {ty0 = ty'; ty1 = ty} >>
      Refiner.unify >>
      C.check ~ty @@ Tm.up cmd >>= function
      | `Ok ->
        M.ret @@ Tm.up cmd
      | `Exn exn ->
        C.dump_state Format.err_formatter "foo" `All >>= fun _ ->
        Format.eprintf "raising exn@.";
        raise exn

  and elab_cut exp frms =
    elab_cut_bwd exp (Bwd.from_list frms)

  and elab_cut_bwd exp frms =
    elab_cut_bwd_ exp frms >>= fun (ty, cmd) ->
    normalize_ty ty >>= fun ty ->
    M.ret (ty, cmd)

  and elab_cut_bwd_ exp frms =
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
            let ty, _ = Tm.unbind_ext_with (List.map (fun tr -> Tm.DownX tr, []) trs0) ebnd in
            go dims1 (ty, cmd @< (Tm.ExtApp trs0))
          | _ ->
            raise ChkMatch
      in
      elab_cut_bwd exp spine >>= go dims

    | spine, `FunApp e ->
      elab_cut_bwd exp spine >>= fun (ty, cmd) ->
      try_nf ty @@ fun ty ->
      begin
        match unleash ty with
        | Tm.Pi (dom, cod) ->
          elab_chk e {ty = dom; sys = []} <<@> fun arg ->
            Tm.unbind_with (Tm.ann ~ty:dom ~tm:arg) cod, cmd @< Tm.FunApp arg
        | _ ->
          raise ChkMatch
      end

    | spine, `Fst ->
      elab_cut_bwd exp spine >>= fun (ty, cmd) ->
      try_nf ty @@ fun ty ->
      begin
        match unleash ty with
        | Tm.Sg (dom, _) ->
          M.ret (dom, cmd @< Tm.Fst)
        | _ ->
          raise ChkMatch
      end


    | spine, `Snd ->
      elab_cut_bwd exp spine >>= fun (ty, cmd) ->
      try_nf ty @@ fun ty ->
      begin
        match unleash ty with
        | Tm.Sg (_dom, cod) ->
          let cod' = Tm.unbind_with (cmd @< Tm.Fst) cod in
          M.ret (cod', cmd @< Tm.Snd)
        | _ ->
          raise ChkMatch
      end

    | spine, `Prev {con = E.Var {name; _}} ->
      elab_var name 0 >>= fun (_, tick) ->
      M.in_scope (Name.fresh ()) (`KillFromTick (Tm.up tick)) begin
        elab_cut_bwd exp spine
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

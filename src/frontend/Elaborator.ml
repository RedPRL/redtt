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

  module E = ESig
  module T = Map.Make (String)

  open Refiner

  type mode =
    | Chk of ty
    | Inf

  let univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kind.Pre

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
    C.bind (C.optional m) @@
    function
    | Some x -> C.ret x
    | None -> n


  let kind_of_frame env =
    function
    | E.App E.TickConst ->
      M.ret @@ `Prev E.TickConst
    | E.App (E.Num (0 | 1) as e) ->
      M.ret @@ `ExtApp e
    | E.App (E.Var (nm, _) as e) ->
      get_resolver env >>= fun renv ->
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
      elab_decl env (E.Debug f) >>= fun env' ->
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

    | E.Data (_dlbl, _edesc) ->
      failwith "Elaborating data declaration"

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
    match Tm.unleash ty, e with
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
          M.emit @@ M.UserHole {name; ty; tele = psi; tm = Tm.up tm}
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
          elab_up env ty @@ E.Quo tmfam
        | _ ->
          M.ret @@ tmfam renv
      end


    | _, E.If (omot, escrut, etcase, efcase) ->
      let tac_mot = Option.map (fun emot ty -> elab_chk env ty emot) omot in
      let tac_scrut ty = elab_chk env ty escrut in
      let tac_tcase ty = elab_chk env ty etcase in
      let tac_fcase ty = elab_chk env ty efcase in
      tac_if ~tac_mot ~tac_scrut ~tac_tcase ~tac_fcase ty

    | _, E.NatRec (omot, escrut, ezcase, (name_scase, name_rec_scase, escase)) ->
      let tac_mot = Option.map (fun emot ty -> elab_chk env ty emot) omot in
      let tac_scrut ty = elab_chk env ty escrut in
      let tac_zcase ty = elab_chk env ty ezcase in
      let tac_scase ty = elab_chk env ty escase in
      tac_nat_rec ~tac_mot ~tac_scrut ~tac_zcase ~tac_scase:(name_scase, name_rec_scase, tac_scase) ty

    | _, E.IntRec (omot, escrut, (name_pcase, epcase), (name_ncase, encase)) ->
      let tac_mot = Option.map (fun emot ty -> elab_chk env ty emot) omot in
      let tac_scrut ty = elab_chk env ty escrut in
      let tac_pcase ty = elab_chk env ty epcase in
      let tac_ncase ty = elab_chk env ty encase in
      tac_int_rec ~tac_mot ~tac_scrut ~tac_pcase:(name_pcase, tac_pcase) ~tac_ncase:(name_ncase, tac_ncase) ty

    | _, E.S1Rec (omot, escrut, ebcase, (name_lcase, elcase)) ->
      let tac_mot = Option.map (fun emot ty -> elab_chk env ty emot) omot in
      let tac_scrut ty = elab_chk env ty escrut in
      let tac_bcase ty = elab_chk env ty ebcase in
      let tac_lcase ty = elab_chk env ty elcase in
      tac_s1_rec ~tac_mot ~tac_scrut ~tac_bcase ~tac_lcase:(name_lcase, tac_lcase) ty

    | Tm.Univ _, E.Bool ->
      M.ret @@ Tm.make Tm.Bool

    | Tm.Bool, E.Tt ->
      M.ret @@ Tm.make Tm.Tt

    | Tm.Bool, E.Ff ->
      M.ret @@ Tm.make Tm.Ff

    | Tm.Univ _, E.Nat ->
      M.ret @@ Tm.make Tm.Nat

    | Tm.Nat, E.Zero ->
      M.ret @@ Tm.make Tm.Zero

    | Tm.Nat, E.Suc n ->
      let nat = Tm.make @@ Tm.Nat in
      elab_chk env nat n <<@> fun n ->
        Tm.make @@ Tm.Suc n

    | Tm.Univ _, E.Int ->
      M.ret @@ Tm.make Tm.Int

    | Tm.Int, E.Pos n ->
      let nat = Tm.make @@ Tm.Nat in
      elab_chk env nat n <<@> fun n ->
        Tm.make @@ Tm.Pos n

    | Tm.Int, E.NegSuc n ->
      let nat = Tm.make @@ Tm.Nat in
      elab_chk env nat n <<@> fun n ->
        Tm.make @@ Tm.NegSuc n

    | Tm.Univ _, E.S1 ->
      M.ret @@ Tm.make Tm.S1

    | Tm.S1, E.Base ->
      M.ret @@ Tm.make Tm.Base

    | Tm.S1, E.Loop r ->
      elab_dim env r <<@> fun r ->
        Tm.make (Tm.Loop r)

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
        elab_chk env ty (E.Pi (etele, ecod))
        <<@> Tm.bind x
        <<@> fun cod -> Tm.make @@ Tm.Pi (dom, cod)
      end

    | Tm.Univ _, E.Pi (`I name :: etele, ecod) ->
      let x = Name.named @@ Some name in
      M.in_scope x `I begin
        elab_chk env ty (E.Pi (etele, ecod))
        <<@> fun codx ->
          let ebnd = Tm.bind_ext (Emp #< x) codx [] in
          Tm.make @@ Tm.Ext ebnd
      end

    | Tm.Univ _, E.Pi (`Tick name :: etele, ecod) ->
      let x = Name.named @@ Some name in
      M.in_scope x `Tick begin
        elab_chk env ty (E.Pi (etele, ecod))
        <<@> Tm.bind x
        <<@> fun bnd -> Tm.make @@ Tm.Later bnd
      end

    | Tm.Univ _, E.Pi (`Lock :: etele, ecod) ->
      let x = Name.fresh () in
      M.in_scope x `Lock begin
        elab_chk env ty (E.Pi (etele, ecod))
        <<@> fun ty -> Tm.make @@ Tm.BoxModality ty
      end

    | Tm.Univ _, E.Sg ([], e) ->
      elab_chk env ty e

    | Tm.Univ _, E.Sg (`Ty (name, edom) :: etele, ecod) ->
      elab_chk env ty edom >>= fun dom ->
      let x = Name.named @@ Some name in
      M.in_scope x (`P dom) begin
        elab_chk env ty (E.Sg (etele, ecod))
        <<@> Tm.bind x
        <<@> fun cod -> Tm.make @@ Tm.Sg (dom, cod)
      end


    | _, Tuple [] ->
      failwith "empty tuple"
    | _, Tuple [e] ->
      elab_chk env ty e
    | Tm.Sg (dom, cod), Tuple (e :: es) ->
      elab_chk env dom e >>= fun tm0 ->
      let cmd0 = Tm.Down {ty = dom; tm = tm0}, Emp in
      let cod' = Tm.make @@ Tm.Let (cmd0, cod) in
      elab_chk env cod' (Tuple es) <<@> Tm.cons tm0

    | Tm.Univ info, Type ->
      begin
        if Lvl.greater info.lvl (Lvl.Const 0) then
          match Tm.unleash ty with
          | Tm.Univ _ ->
            M.ret @@ Tm.univ ~kind:Kind.Kan ~lvl:(Lvl.Const 0)
          | _ ->
            failwith "Type"
        else
          failwith "Elaborator: universe level error"
      end

    | _, E.Cut (e, fs) ->
      elab_chk_cut env e fs ty
      <<@> snd
      <<@> Tm.up

    | _, E.HCom info ->
      elab_dim env info.r >>= fun r ->
      elab_dim env info.r' >>= fun r' ->
      let kan_univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kan in
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

    | _, e ->
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
    match e with
    | E.Var (name, ushift) ->
      elab_var env name ushift >>= fun (a, cmd) ->
      M.lift (C.lookup_var a `Only <+> C.bind (C.lookup_meta a) (fun (ty, _) -> C.ret ty)) <<@> fun ty ->
        Tm.shift_univ ushift ty, cmd

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

    | E.Suc n ->
      let nat = Tm.make Tm.Nat in
      elab_chk env nat n <<@> fun n ->
        nat, (Tm.Down {ty = nat; tm = Tm.make (Tm.Suc n)}, Emp)

    | E.Zero ->
      M.ret @@
      let nat = Tm.make Tm.Nat in
      nat, (Tm.Down {ty = nat; tm = Tm.make Tm.Zero}, Emp)

    | E.Cut (e, fs) ->
      elab_cut env e fs >>= fun (vty, cmd) ->
      M.lift C.base_cx <<@> fun cx ->
        let ty = Cx.quote_ty cx vty in
        ty, cmd

    | E.Coe info ->
      elab_dim env info.r >>= fun tr ->
      elab_dim env info.r' >>= fun tr' ->
      let x = Name.fresh () in
      let kan_univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kind.Kan in
      let univ_fam = Tm.make @@ Tm.Ext (Tm.bind_ext (Emp #< x) kan_univ []) in
      elab_chk env univ_fam info.fam >>= fun fam ->
      begin
        (M.lift @@ (univ_fam, fam) %% Tm.ExtApp [tr] <<@> snd)
        <&>
        (M.lift @@ (univ_fam, fam) %% Tm.ExtApp [tr'] <<@> snd)
      end >>= fun (fam_r, fam_r') ->
      elab_chk env fam_r info.tm <<@> fun tm ->
        let varx = Tm.up @@ Tm.var x in
        let tyx = Tm.up (Tm.Down {ty = univ_fam; tm = fam}, Emp #< (Tm.ExtApp [varx])) in
        let coe = Tm.Coe {r = tr; r' = tr'; ty = Tm.bind x tyx; tm} in
        fam_r', (coe, Emp)

    | E.Com info ->
      elab_dim env info.r >>= fun tr ->
      elab_dim env info.r' >>= fun tr' ->
      let x = Name.fresh () in
      let kan_univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kind.Kan in
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
          ty, (Tm.Down {tm = fix; ty}, Emp)
      end

    | _ ->
      failwith "Can't infer"

  and elab_dim env e =
    match e with
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
          go spine (dim :: dims)
        | _ ->
          M.ret (spine #< frm, Bwd.from_list dims)
    in
    go spine []


  and evaluator =
    M.lift C.base_cx <<@> fun cx ->
      cx, Cx.evaluator cx

  and traverse f xs =
    match xs with
    | [] ->
      M.ret []
    | x :: xs ->
      (fun y ys -> y :: ys) <@>> f x <*> traverse f xs

  and elab_chk_cut env exp frms ty =
    elab_cut env exp frms >>= fun (vty, cmd) ->
    M.lift C.base_cx >>= fun cx ->
    let ty' = Cx.quote_ty cx vty in
    M.lift @@ C.active @@ Dev.Subtype {ty0 = ty'; ty1 = ty} >>
    M.unify >>
    M.lift (C.check_subtype ty' ty) >>= function
    | `Ok ->
      M.ret (ty, cmd)
    | `Exn exn ->
      raise exn


  and elab_cut env exp frms =
    bite_from_spine env frms >>= function
    | _, `Done ->
      elab_inf env exp >>= fun (ty, cmd) ->
      M.lift @@ Unify.eval ty <<@> fun vty ->
          vty, cmd

    | spine, `ExtApp dims ->
      let rec go dims (vty, (hd, sp)) =
        match dims with
        | [] ->
          M.ret (vty, (hd, sp))
        | _ ->
          evaluator >>= fun (cx, (module V)) ->
          let n = Domain.ExtAbs.len @@ V.unleash_ext vty in
          let dims0, dims1 = ListUtil.split n dims in
          traverse (elab_dim env) dims0 >>= fun trs0 ->
          let rs0 = List.map (Cx.eval_dim cx) trs0 in
          let ty, _ = V.unleash_ext_with vty rs0 in
          go dims1 (ty, (hd, sp #< (Tm.ExtApp trs0)))
      in

      elab_cut env exp spine >>= go dims

    | spine, `FunApp e ->
      elab_cut env exp spine >>= fun (vty, (hd, sp)) ->
      evaluator >>= fun (cx, (module V)) ->
      let dom, cod = V.unleash_pi vty in
      let tdom = Cx.quote_ty cx dom in
      elab_chk env tdom e >>= fun arg ->
      evaluator <<@> fun (cx, (module V)) ->
        let varg = Cx.eval cx arg in
        V.inst_clo cod varg, (hd, sp #< (Tm.FunApp arg))

    | spine, `Car ->
      elab_cut env exp spine >>= fun (vty, (hd, sp)) ->
      evaluator <<@> fun (_, (module V)) ->
        let dom, _ = V.unleash_sg vty in
        dom, (hd, sp #< Tm.Car)

    | spine, `Cdr ->
      elab_cut env exp spine >>= fun (vty, (hd, sp)) ->
      evaluator <<@> fun (cx, (module V)) ->
        let _, cod = V.unleash_sg vty in
        let cod' = V.inst_clo cod @@ Cx.eval_cmd cx (hd, sp #< Tm.Car) in
        cod', (hd, sp #< Tm.Cdr)

    | spine, `Prev E.TickConst ->
      M.in_scope (Name.fresh ()) `Lock begin
        elab_cut env exp spine
      end >>= fun (vty, (hd, sp)) ->
      evaluator <<@> fun (_, (module V)) ->
        let tclo = V.unleash_later vty in
        let tick = Tm.make Tm.TickConst in
        let vty' = V.inst_tick_clo tclo @@ Domain.TickConst in
        vty', (hd, sp #< (Tm.Prev tick))

    | spine, `Prev (E.Var (name, _)) ->
      elab_var env name 0 >>= fun (_, tick) ->
      M.in_scope (Name.fresh ()) (`KillFromTick (Tm.up tick)) begin
        elab_cut env exp spine
      end >>= fun (vty, (hd, sp)) ->
      evaluator <<@> fun (cx, (module V)) ->
        let tclo = V.unleash_later vty in
        let vtck = Cx.eval_tick cx (Tm.up tick) in
        let vty' = V.inst_tick_clo tclo vtck in
        vty', (hd, sp #< (Tm.Prev (Tm.up tick)))

    | spine, `Open ->
      M.in_scope (Name.fresh ()) `ClearLocks begin
        elab_cut env exp spine
      end >>= fun (vty, (hd, sp)) ->
      evaluator <<@> fun (_, (module V)) ->
        let vty' = V.unleash_box_modality vty in
        vty', (hd, sp #< Tm.Open)

    | _ ->
      failwith "elab_cut"


end


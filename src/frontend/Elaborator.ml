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
    M.lift C.ask >>= fun psi ->
    let renv = go_globals (ResEnv.init ()) @@ T.bindings env in
    M.ret @@ go_locals renv psi

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
      elab_scheme env scheme @@ fun cod ->
      M.unify >>
      elab_chk env cod e >>= fun tm ->
      let alpha = Name.named @@ Some name in

      M.lift C.ask >>= fun psi ->
      M.lift @@ U.define psi alpha opacity cod tm >>= fun _ ->
      M.lift C.go_to_top >>
      M.unify >>= fun _ ->
      Format.printf "Defined %s.@." name;
      M.ret @@ T.add name alpha env

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
      end >>= fun tm ->
      M.ret @@ Tm.make @@ Tm.Shut tm

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
      M.lift @@ U.push_hole `Flex psi ty >>= fun tm ->
      M.ret @@ Tm.up tm


    | _, E.Let info ->
      let itac =
        match info.ty with
        | None ->
          elab_inf env info.tm >>= fun (let_ty, let_tm) ->
          M.ret (let_ty, Tm.up let_tm)
        | Some ety ->
          elab_chk env univ ety >>= fun let_ty ->
          elab_chk env let_ty info.tm >>= fun let_tm ->
          M.ret (let_ty, let_tm)
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
      elab_chk env nat n >>= fun n ->
      M.ret @@ Tm.make @@ Tm.Suc n

    | Tm.Univ _, E.Int ->
      M.ret @@ Tm.make Tm.Int

    | Tm.Int, E.Pos n ->
      let nat = Tm.make @@ Tm.Nat in
      elab_chk env nat n >>= fun n ->
      M.ret @@ Tm.make @@ Tm.Pos n

    | Tm.Int, E.NegSuc n ->
      let nat = Tm.make @@ Tm.Nat in
      elab_chk env nat n >>= fun n ->
      M.ret @@ Tm.make @@ Tm.NegSuc n

    | Tm.Univ _, E.S1 ->
      M.ret @@ Tm.make Tm.S1

    | Tm.S1, E.Base ->
      M.ret @@ Tm.make Tm.Base

    | Tm.S1, E.Loop r ->
      elab_dim env r >>= fun r ->
      M.ret @@ Tm.make (Tm.Loop r)

    | Tm.Univ _, E.Ext (names, ety, esys) ->
      let univ = ty in
      let xs = List.map (fun x -> Name.named (Some x)) names in
      let ps = List.map (fun x -> (x, `I)) xs in
      M.in_scopes ps
        begin
          elab_chk env univ ety >>= fun ty ->
          elab_tm_sys env ty esys >>= fun sys ->
          M.ret (ty, sys)
        end >>= fun (tyxs, sysxs) ->
      let ebnd = Tm.bind_ext (Bwd.from_list xs) tyxs sysxs in
      let ext_ty = Tm.make @@ Tm.Ext ebnd in
      M.ret ext_ty

    | Tm.Univ _, E.Rst (ety, esys) ->
      let univ = ty in
      elab_chk env univ ety >>= fun ty ->
      elab_tm_sys env ty esys >>= fun sys ->
      M.ret @@ Tm.make @@ Tm.Rst {ty; sys}

    | Tm.Univ _, E.Pi ([], e) ->
      elab_chk env ty e

    | Tm.Univ _, E.Pi (`Ty (name, edom) :: etele, ecod) ->
      elab_chk env ty edom >>= fun dom ->
      let x = Name.named @@ Some name in
      M.in_scope x (`P dom) begin
        elab_chk env ty @@ E.Pi (etele, ecod)
      end >>= fun codx ->
      M.ret @@ Tm.make @@ Tm.Pi (dom, Tm.bind x codx)

    | Tm.Univ _, E.Pi (`I name :: etele, ecod) ->
      let x = Name.named @@ Some name in
      M.in_scope x `I begin
        elab_chk env ty @@ E.Pi (etele, ecod)
      end >>= fun codx ->
      let ebnd = Tm.bind_ext (Emp #< x) codx [] in
      M.ret @@ Tm.make @@ Tm.Ext ebnd

    | Tm.Univ _, E.Pi (`Tick name :: etele, ecod) ->
      let x = Name.named @@ Some name in
      M.in_scope x `Tick begin
        elab_chk env ty @@ E.Pi (etele, ecod)
      end >>= fun codx ->
      let bnd = Tm.bind x codx in
      M.ret @@ Tm.make @@ Tm.Later bnd

    | Tm.Univ _, E.Pi (`Lock :: etele, ecod) ->
      let x = Name.fresh () in
      M.in_scope x `Lock begin
        elab_chk env ty @@ E.Pi (etele, ecod)
      end >>= fun ty ->
      M.ret @@ Tm.make @@ Tm.BoxModality ty

    | Tm.Univ _, E.Sg ([], e) ->
      elab_chk env ty e

    | Tm.Univ _, E.Sg (`Ty (name, edom) :: etele, ecod) ->
      elab_chk env ty edom >>= fun dom ->
      let x = Name.named @@ Some name in
      M.in_scope x (`P dom) begin
        elab_chk env ty @@ E.Sg (etele, ecod)
      end >>= fun codx ->
      M.ret @@ Tm.make @@ Tm.Sg (dom, Tm.bind x codx)


    | _, Tuple [] ->
      failwith "empty tuple"
    | _, Tuple [e] ->
      elab_chk env ty e
    | Tm.Sg (dom, cod), Tuple (e :: es) ->
      elab_chk env dom e >>= fun tm0 ->
      let cmd0 = Tm.Down {ty = dom; tm = tm0}, Emp in
      let cod' = Tm.make @@ Tm.Let (cmd0, cod) in
      elab_chk env cod' (Tuple es) >>= fun tm1 ->
      M.ret @@ Tm.cons tm0 tm1

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
      elab_inf env e >>= fun (hty, hd) ->
      normalize_ty hty >>= fun hty ->

      elab_cut env (hty, hd) fs (Chk ty) >>= fun (_, tm) ->
      M.ret @@ Tm.up tm

    | _, E.HCom info ->
      elab_dim env info.r >>= fun r ->
      elab_dim env info.r' >>= fun r' ->
      let kan_univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kan in
      begin
        M.lift @@ C.check ~ty:kan_univ ty >>= function
        | `Ok ->
          elab_chk env ty info.cap >>= fun cap ->
          elab_hcom_sys env r ty cap info.sys >>= fun sys ->
          let hcom = Tm.HCom {r; r'; ty; cap; sys} in
          M.ret @@ Tm.up (hcom, Emp)

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

  and elab_inf env e : (ty * tm Tm.cmd) M.m =
    match e with
    | E.Var (name, ushift) ->
      get_resolver env >>= fun renv ->
      begin
        match ResEnv.get name renv with
        | `Var a ->
          M.lift (C.lookup_var a `Only <+> C.bind (C.lookup_meta a) (fun (ty, _) -> C.ret ty)) >>= fun ty ->
          let ty = Tm.shift_univ ushift ty in
          let cmd = Tm.Var {name = a; twin = `Only; ushift}, Emp in
          M.ret (ty, cmd)
        | `Ix _ ->
          failwith "elab_inf: expected locally closed"
      end

    | E.Quo tmfam ->
      get_resolver env >>= fun renv ->
      let tm = tmfam renv in
      begin
        match Tm.unleash tm with
        | Tm.Up cmd ->
          M.lift C.base_cx >>= fun cx ->
          let vty = Typing.infer cx cmd in
          M.ret (Cx.quote_ty cx vty, cmd)
        | _ ->
          failwith "Cannot elaborate `term"
      end

    | E.Suc n ->
      let nat = Tm.make Tm.Nat in
      elab_chk env nat n >>= fun n ->
      M.ret (nat, (Tm.Down {ty = nat; tm = Tm.make (Tm.Suc n)}, Emp))

    | E.Zero ->
      let nat = Tm.make Tm.Nat in
      M.ret (nat, (Tm.Down {ty = nat; tm = Tm.make Tm.Zero}, Emp))

    | E.Cut (e, fs) ->
      fancy_elab_cut env e (Bwd.from_list fs) >>= fun (vty, cmd) ->
      M.lift C.base_cx >>= fun cx ->
      let ty = Cx.quote_ty cx vty in
      M.ret (ty, cmd)

    | E.Coe info ->
      elab_dim env info.r >>= fun tr ->
      elab_dim env info.r' >>= fun tr' ->
      let x = Name.fresh () in
      let kan_univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kind.Kan in
      let univ_fam = Tm.make @@ Tm.Ext (Tm.bind_ext (Emp #< x) kan_univ []) in
      elab_chk env univ_fam info.fam >>= fun fam ->
      M.in_scope x `I begin
        M.lift @@ (univ_fam, fam) %% Tm.ExtApp [tr] >>= fun (_, fam_r) ->
        M.lift @@ (univ_fam, fam) %% Tm.ExtApp [tr'] >>= fun (_, fam_r') ->
        M.ret (fam_r, fam_r')
      end >>= fun (fam_r, fam_r') ->
      elab_chk env fam_r info.tm >>= fun tm ->
      let varx = Tm.up @@ Tm.var x in
      let tyx = Tm.up (Tm.Down {ty = univ_fam; tm = fam}, Emp #< (Tm.ExtApp [varx])) in
      let coe = Tm.Coe {r = tr; r' = tr'; ty = Tm.bind x tyx; tm} in
      M.ret (fam_r', (coe, Emp))

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
      let varx = Tm.up @@ Tm.var x in
      M.in_scope x `I begin
        M.lift @@ (univ_fam, fam) %% Tm.ExtApp [varx]
      end >>= fun (_, fam_x) ->
      let tybnd = Tm.bind x fam_x in
      elab_com_sys env tr tybnd cap info.sys >>= fun sys ->
      let com = Tm.Com {r = tr; r' = tr'; ty = tybnd; cap; sys} in
      M.ret (fam_r', (com, Emp))

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
        bite_dims_from_spine env spine >>= fun (spine, dims) ->
        M.ret (spine, `ExtApp (Bwd.to_list @@ dims #< dim))
      | `Prev e ->
        M.ret (spine, `Prev e)
      | `Car ->
        M.ret (spine, `Car)
      | `Cdr ->
        M.ret (spine, `Cdr)

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
    M.lift C.base_cx >>= fun cx ->
    M.ret (cx, Cx.evaluator cx)

  and traverse f xs =
    match xs with
    | [] ->
      M.ret []
    | x :: xs ->
      f x >>= fun y ->
      traverse f xs >>= fun ys ->
      M.ret (y :: ys)

  and fancy_elab_cut env exp frms =
    bite_from_spine env frms >>= function
    | _, `Done ->
      elab_inf env exp >>= fun (ty, cmd) ->
      M.lift @@ Unify.eval ty >>= fun vty ->
      M.ret (vty, cmd)

    | spine, `ExtApp dims ->
      evaluator >>= fun (cx, (module V)) ->

      let rec go dims (vty, (hd, sp)) =
        match dims with
        | [] ->
          M.ret (vty, (hd, sp))
        | _ ->
          let n = Domain.ExtAbs.len @@ V.unleash_ext vty in
          let dims0, dims1 = ListUtil.split n dims in
          traverse (elab_dim env) dims0 >>= fun trs0 ->
          let rs0 = List.map (Cx.eval_dim cx) trs0 in
          let ty, _ = V.unleash_ext_with vty rs0 in
          go dims1 (ty, (hd, sp #< (Tm.ExtApp trs0)))
      in

      fancy_elab_cut env exp spine >>= go dims

    | spine, `FunApp e ->
      fancy_elab_cut env exp spine >>= fun (vty, (hd, sp)) ->
      evaluator >>= fun (cx, (module V)) ->
      let dom, cod = V.unleash_pi vty in
      let tdom = Cx.quote_ty cx dom in
      elab_chk env tdom e >>= fun arg ->
      let varg = Cx.eval cx arg in
      M.ret (V.inst_clo cod varg, (hd, sp #< (Tm.FunApp arg)))

    | spine, `Car ->
      fancy_elab_cut env exp spine >>= fun (vty, (hd, sp)) ->
      evaluator >>= fun (_, (module V)) ->
      let dom, _ = V.unleash_sg vty in
      M.ret (dom, (hd, sp #< Tm.Car))

    | spine, `Cdr ->
      fancy_elab_cut env exp spine >>= fun (vty, (hd, sp)) ->
      evaluator >>= fun (cx, (module V)) ->
      let _, cod = V.unleash_sg vty in
      let cod' = V.inst_clo cod @@ Cx.eval_cmd cx (hd, sp #< Tm.Car) in
      M.ret (cod', (hd, sp #< Tm.Cdr))

    | _, `Prev _ ->
      failwith ""


  and elab_cut : _ -> (ty * tm Tm.cmd) -> E.frame list -> mode -> (ty * tm Tm.cmd) M.m =
    fun env ->
      let rec go : ty -> _ -> _ -> mode -> _ M.m =
        fun (hty : ty) (hd, sp) efs mode : _ M.m ->
          match Tm.unleash hty, efs with
          | _, [] ->
            begin
              match mode with
              | Chk ty ->
                begin
                  M.lift (C.check_subtype hty ty) >>= function
                  | `Ok ->
                    M.ret (ty, (hd, sp))
                  | _ ->
                    M.lift @@ C.active @@ Dev.Subtype {ty0 = hty; ty1 = ty} >>
                    M.unify >>
                    M.lift (C.check_subtype hty ty) >>= function
                    | `Ok ->
                      M.ret (ty, (hd, sp))
                    | `Exn exn ->
                      raise exn
                end

              | Inf ->
                M.ret (hty, (hd, sp))
            end

          | Tm.Pi (dom, cod), E.App e :: efs ->
            elab_chk env dom e >>= fun t ->
            M.lift @@ Unify.eval dom >>= fun vdom ->
            M.lift @@ Unify.inst_ty_bnd cod (vdom, t) >>= fun cod' ->
            go cod' (hd, sp #< (Tm.FunApp t)) efs mode

          | Tm.Ext ebnd, efs ->
            let xs, ext_ty, _ = Tm.unbind_ext ebnd in
            let rec bite rs xs efs =
              match xs, efs with
              | Emp, _ ->
                M.ret (rs, efs)
              | Snoc (xs, _), E.App e :: efs ->
                elab_dim env e >>= fun r ->
                bite (rs #< r) xs efs
              | _ ->
                failwith "elab_cut: problem biting extension type"
            in
            bite Emp xs efs >>= fun (rs, efs) ->
            let rs = Bwd.to_list rs in
            let restriction = List.map2 (fun x r -> Name.fresh (), `R (Tm.up @@ Tm.var x, r)) (Bwd.to_list xs) rs in
            M.in_scopes restriction begin
              normalize_ty ext_ty >>= fun ext_ty ->
              go ext_ty (hd, sp #< (Tm.ExtApp rs)) efs mode
            end

          | Tm.Sg (dom, _), E.Car :: efs ->
            go dom (hd, sp #< Tm.Car) efs mode

          | Tm.Sg (_, Tm.B (_, cod)), E.Cdr :: efs ->
            let cod' = Tm.subst (Tm.dot (hd, sp #< Tm.Car) (Tm.shift 0)) cod in
            go cod' (hd, sp #< Tm.Cdr) efs mode

          | Tm.Rst rst, efs ->
            go rst.ty (hd, sp) efs mode

          | _ ->
            Format.eprintf "damn: %a@." Tm.pp0 hty;
            failwith "elab_cut: unexpected case"
      in
      fun (hty, cmd) ->
        go hty cmd

end


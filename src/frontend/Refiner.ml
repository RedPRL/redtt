open RedBasis
open RedTT_Core
open Dev open Bwd open BwdNotation

module D = Domain
module M = ElabMonad
module C = Contextual
module U = Unify
module Notation = Monad.Notation (M)
open Notation

type chk_tac = ty -> tm M.m
type inf_tac = (ty * tm) M.m

open Tm.Notation


let normalization_clock = ref 0.

let _ =
  Diagnostics.on_termination @@ fun _ ->
  Format.eprintf "Refine spent %fs in normalizing types@." !normalization_clock

let normalize_ty ty =
  let now0 = Unix.gettimeofday () in
  M.lift C.base_cx >>= fun cx ->
  let vty = Cx.eval cx ty in
  let ty = Cx.quote_ty cx vty in
  let now1 = Unix.gettimeofday () in
  normalization_clock := !normalization_clock +. (now1 -. now0);
  M.ret ty


let guess_restricted ty sys tm =
  let rty = Tm.make @@ Tm.Rst {ty; sys} in
  M.lift @@ C.check ~ty:rty tm >>= function
  | `Ok -> M.ret tm
  | _ ->
    let rec go =
      function
      | [] ->
        M.ret ()
      | (r, r', Some tm') :: sys ->
        begin
          M.under_restriction r r' @@
          M.lift @@ C.active @@ Unify {ty0 = ty; ty1 = ty; tm0 = tm; tm1 = tm'}
        end >>
        go sys
      | _ :: sys ->
        go sys
    in
    go sys >>
    M.unify >>
    M.lift @@ C.check ~ty:rty tm >>= function
    | `Ok -> M.ret tm
    | `Exn exn ->
      raise exn

exception ChkMatch

let rec tac_rst tac ty =
  let rec go sys ty =
    normalize_ty ty >>= fun ty ->
    match Tm.unleash ty with
    | Tm.Rst rst ->
      go (rst.sys @ sys) rst.ty
    | _ ->
      begin
        match sys with
        | [] -> tac ty
        | _ ->
          normalize_ty ty >>= fun ty ->
          tac_wrap_nf tac ty >>=
          guess_restricted ty sys
      end
  in go [] ty


and tac_wrap_nf tac ty =
  try tac ty
  with
  | ChkMatch ->
    normalize_ty ty >>=
    tac_rst tac


let tac_let name itac ctac =
  fun ty ->
    itac >>= fun (let_ty, let_tm) ->
    (* let singleton_ty =
       let face = Tm.make Tm.Dim0, Tm.make Tm.Dim0, Some let_tm in
       Tm.make @@ Tm.Rst {ty = let_ty; sys = [face]}
       in *)
    let x = Name.named @@ Some name in
    M.in_scope x (`Def (let_ty, let_tm)) (ctac ty) >>= fun bdyx ->
    M.ret @@ Tm.make @@ Tm.Let (Tm.ann ~ty:let_ty ~tm:let_tm, Tm.bind x bdyx)


let rec tac_lambda names tac ty =
  match Tm.unleash ty with
  | Tm.Pi (dom, cod) ->
    begin
      match names with
      | [] -> tac ty
      | name :: names ->
        let x = Name.named @@ Some name in
        let codx = Tm.unbind_with (Tm.var x) cod in
        M.in_scope x (`P dom) begin
          tac_wrap_nf (tac_lambda names tac) codx
        end >>= fun bdyx ->
        M.ret @@ Tm.make @@ Tm.Lam (Tm.bind x bdyx)
    end

  | Tm.Later cod ->
    begin
      match names with
      | [] -> tac ty
      | name :: names ->
        let x = Name.named @@ Some name in
        let codx = Tm.unbind_with (Tm.var x) cod in
        M.in_scope x `Tick begin
          tac_wrap_nf (tac_lambda names tac) codx
        end >>= fun bdyx ->
        M.ret @@ Tm.make @@ Tm.Next (Tm.bind x bdyx)
    end

  | Tm.Ext (Tm.NB (nms, _) as ebnd) ->
    begin
      match names with
      | [] -> tac ty
      | _ ->
        let rec bite nms lnames rnames =
          match nms, rnames with
          | Emp, _ -> lnames, tac_wrap_nf (tac_lambda rnames tac)
          | Snoc (nms, _), name :: rnames ->
            let x = Name.named @@ Some name in
            bite nms (lnames #< x) rnames
          | _ -> failwith "Elab: incorrect number of binders when refining extension type"
        in
        let xs, tac' = bite nms Emp names in
        let ty, sys = Tm.unbind_ext_with (Bwd.to_list @@ Bwd.map (fun x -> Tm.var x) xs) ebnd in
        let rty = Tm.make @@ Tm.Rst {ty; sys} in
        let ps = List.map (fun x -> (x, `I)) @@ Bwd.to_list xs in
        M.in_scopes ps begin
          tac' rty
        end >>= fun bdyxs ->
        let lam = Tm.make @@ Tm.ExtLam (Tm.bindn xs bdyxs) in
        M.ret lam
    end

  | _ ->
    begin
      match names with
      | [] -> tac ty
      | _ ->
        raise ChkMatch
    end

(* TODO factor out the motive inference algorithm *)

let unleash_data ty =
  match Tm.unleash ty with
  | Tm.Data dlbl -> dlbl
  | _ ->
    Format.eprintf "Dang: %a@." Tm.pp0 ty;
    failwith "Expected datatype"

let guess_motive scrut ty =
  match Tm.unleash scrut with
  | Tm.Up (Tm.Var var, Emp) ->
    M.ret @@ Tm.bind var.name ty
  | _ ->
    M.ret @@ Tm.bind (Name.fresh ()) ty

let make_motive ~data_ty ~tac_mot ~scrut ~ty =
  match tac_mot with
  | None ->
    guess_motive scrut ty
  | Some tac_mot ->
    let univ = Tm.univ ~lvl:`Omega ~kind:`Pre in
    let mot_ty = Tm.pi None data_ty univ in
    tac_mot mot_ty >>= fun mot ->
    let motx =
      Tm.ann ~ty:(Tm.subst (Tm.shift 1) mot_ty) ~tm:(Tm.subst (Tm.shift 1) mot)
      @< Tm.FunApp (Tm.up @@ Tm.ix 0)
    in
    M.ret @@ Tm.B (None, Tm.up @@ motx)

let tac_elim ~loc ~tac_mot ~tac_scrut ~clauses : chk_tac =
  fun ty ->
    tac_scrut >>= fun (data_ty, scrut) ->
    normalize_ty data_ty >>= fun data_ty ->

    make_motive ~data_ty ~scrut ~tac_mot ~ty >>= fun bmot ->

    let mot arg =
      let Tm.B (_, motx) = bmot in
      let arg' = Tm.ann ~ty:data_ty ~tm:arg in
      Tm.subst (Tm.dot arg' (Tm.shift 0)) motx
    in

    let dlbl = unleash_data data_ty in
    let data_vty = D.make @@ D.Data dlbl in

    begin
      M.lift C.base_cx <<@> fun cx ->
        GlobalEnv.lookup_datatype dlbl @@ Cx.globals cx
    end >>= fun desc ->

    (* Add holes for any missing clauses *)
    let clauses =
      let find_clause lbl =
        try
          List.find (fun (lbl', _, _) -> lbl = lbl') clauses
        with
        | _ ->
          let constr = Desc.lookup_constr lbl desc in
          let pbinds =
            List.map (fun (nm, _) -> ESig.PVar nm) constr.const_specs
            @ List.mapi (fun i _ -> let x = "x" ^ string_of_int i in ESig.PIndVar (x, x ^ "/ih")) constr.rec_specs
            @ List.map (fun x -> ESig.PVar x) constr.dim_specs
          in
          lbl, pbinds, fun ty ->
            M.lift C.ask >>= fun psi ->
            M.lift @@ U.push_hole `Rigid psi ty >>= fun tm ->
            M.emit loc @@ M.UserHole {name = Some lbl; ty; tele = psi; tm = Tm.up tm} >>
            M.ret @@ Tm.up tm
      in
      List.map (fun (lbl, _) -> find_clause lbl) desc.constrs
    in

    begin
      M.lift C.base_cx <<@> fun cx ->
        Cx.evaluator cx, Cx.quoter cx
    end >>= fun ((module V), (module Q)) ->


    (* TODO: factor this out into another tactic. *)
    let refine_clause earlier_clauses (clbl, pbinds, (clause_tac : chk_tac)) =
      let open Desc in
      let constr = lookup_constr clbl desc in
      let rec go psi env (tms, cargs, rargs, rs) pbinds const_specs rec_specs dims =
        match pbinds, const_specs, rec_specs, dims with
        | ESig.PVar nm :: pbinds, (_plbl, pty) :: const_specs, _, _->
          let x = Name.named @@ Some nm in
          let vty = V.eval env pty in
          let tty = Q.quote_ty Quote.Env.emp vty in
          let x_el = V.reflect vty (D.Var {name = x; twin = `Only; ushift = 0}) [] in
          let x_tm = Tm.up @@ Tm.var x in
          let env' = D.Env.push (`Val x_el) env in
          go (psi #< (x, `P tty)) env' (tms #< x_tm, cargs #< x_el, rargs, rs) pbinds const_specs rec_specs dims

        | ESig.PVar nm :: pbinds, [], (_, Self) :: rec_specs, _ ->
          let x = Name.named @@ Some nm in
          let x_ih = Name.fresh () in
          let x_tm = Tm.up @@ Tm.var x in
          let x_el = V.reflect data_vty (D.Var {name = x; twin = `Only; ushift = 0}) [] in
          let ih_ty = mot x_tm in
          go (psi #< (x, `P data_ty) #< (x_ih, `P ih_ty)) env (tms #< x_tm, cargs, rargs #< x_el, rs) pbinds const_specs rec_specs dims

        | ESig.PIndVar (nm, nm_ih) :: pbinds, [], (_, Self) :: rec_specs, _ ->
          let x = Name.named @@ Some nm in
          let x_ih = Name.named @@ Some nm_ih in
          let x_tm = Tm.up @@ Tm.var x in
          let ih_ty = mot x_tm in
          let x_el = V.reflect data_vty (D.Var {name = x; twin = `Only; ushift = 0}) [] in
          go (psi #< (x, `P data_ty) #< (x_ih, `P ih_ty)) env (tms #< x_tm, cargs, rargs #< x_el, rs) pbinds const_specs rec_specs dims

        | ESig.PVar nm :: pbinds, [], [], _ :: dims ->
          let x = Name.named @@ Some nm in
          let x_tm = Tm.up @@ Tm.var x in
          let r = `Atom x in
          let env' = D.Env.push (`Dim r) env in
          go (psi #< (x, `I)) env' (tms #< x_tm, cargs, rargs, rs #< r) pbinds [] [] dims

        | _, [], [], [] ->
          psi, Bwd.to_list tms, Bwd.to_list cargs, Bwd.to_list rargs, Bwd.to_list rs

        | _ ->
          failwith "refine_clause"
      in
      let psi, tms, const_args, rec_args, rs =
        go Emp D.Env.emp (Emp, Emp, Emp, Emp) pbinds constr.const_specs constr.rec_specs constr.dim_specs
      in
      let intro = Tm.make @@ Tm.Intro (dlbl, clbl, tms) in
      let clause_ty = mot intro in

      M.in_scopes (Bwd.to_list psi) begin
        begin
          M.lift C.base_cx <<@> fun cx ->
            cx, Cx.evaluator cx, Cx.quoter cx
        end >>= fun (cx, (module V), (module Q)) ->

        let image_of_face face =
          let elim_face r r' scrut =
            let phi = I.equate r r' in
            let rho = D.Env.act phi @@ Cx.env cx in
            let mot = V.make_closure rho bmot in
            let clauses = List.map (fun (clbl, nbnd) -> clbl, D.NClo {nbnd; rho}) earlier_clauses in
            V.elim_data dlbl ~mot:mot ~scrut:scrut ~clauses
          in
          Face.map elim_face @@
          let env0 = D.Env.clear_locals @@ Cx.env cx in
          V.eval_bterm_face dlbl desc env0 face
            ~const_args
            ~rec_args
            ~rs
        in

        (* What is the image of the boundary in the current fiber of the motive? *)
        let tsys =
          let val_sys = List.map image_of_face constr.boundary in
          let vty = Cx.eval cx clause_ty in
          Q.quote_val_sys (Cx.qenv cx) vty val_sys
        in

        (* We run the clause tactic with the goal type restricted by the boundary above *)
        let clause_rty =
          match tsys with
          | [] -> clause_ty
          | _ -> Tm.make @@ Tm.Rst {ty = clause_ty; sys = tsys}
        in

        clause_tac clause_rty <<@> fun bdy ->
          clbl, Tm.bindn (Bwd.map fst psi) bdy
      end
    in

    let rec refine_clauses acc =
      function
      | [] ->
        M.ret acc
      | clause :: clauses ->
        refine_clause acc clause >>= fun tclause ->
        refine_clauses (tclause :: acc) clauses
    in

    refine_clauses [] clauses >>= fun tclauses ->

    let bmot =
      let x = Name.fresh () in
      Tm.bind x @@ mot @@ Tm.up @@ Tm.var x
    in
    M.ret @@ Tm.up @@
    Tm.ann ~ty:data_ty ~tm:scrut
    @< Tm.Elim {dlbl; mot = bmot; clauses = tclauses}

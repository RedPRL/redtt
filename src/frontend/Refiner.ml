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

(* The idea of this function is to push a restriction downward into a negative type.
   It is perhaps a bit too ambitious to fully unleash, until we have developed the Immortal
   subtyping and definitional equivalence theory that really gets down with eta laws of
   restriction types. *)
let push_restriction sys ty =
  normalize_ty ty >>= fun ty ->
  let on_sys f =
    List.map @@ fun (r, r', otm) ->
    r, r', Option.map f otm
  in
  match Tm.unleash ty with
  | Tm.Pi (dom, cod) ->
    let x, codx = Tm.unbind cod in
    let app_tm tm =
      let var = Tm.up @@ Tm.var x in
      let hd = Tm.Down {ty; tm} in
      Tm.up (hd, Emp #< (Tm.FunApp var))
    in
    let app_sys = on_sys app_tm sys in
    let rcodx = Tm.make @@ Tm.Rst {ty = codx; sys = app_sys} in
    let rty = Tm.make @@ Tm.Pi (dom, Tm.bind x rcodx) in
    M.ret @@ `Negative rty

  | Tm.Ext ebnd ->
    let xs, tyxs, sysxs = Tm.unbind_ext ebnd in
    let app_tm tm =
      let vars = List.map (fun x -> Tm.up @@ Tm.var x) @@ Bwd.to_list xs in
      let hd = Tm.Down {ty; tm} in
      Tm.up (hd , Emp #< (Tm.ExtApp vars))
    in
    let ebnd' = Tm.bind_ext xs tyxs @@ sysxs @ on_sys app_tm sys in
    let rty = Tm.make @@ Tm.Ext ebnd' in
    M.ret @@ `Negative rty

  (* | Tm.Sg (dom, cod) ->
     let car tm = Tm.up (Tm.Down {ty; tm}, Emp #< Tm.Car) in
     let cdr tm = Tm.up (Tm.Down {ty; tm}, Emp #< Tm.Cdr) in
     let x, codx = Tm.unbind cod in
     let rdom = Tm.make @@ Tm.Rst {ty = dom; sys = on_sys car sys} in
     let rcodx = Tm.make @@ Tm.Rst {ty = codx; sys = on_sys cdr sys} in
     let rty = Tm.make @@ Tm.Sg (rdom, Tm.bind x rcodx) in
     M.ret @@ `Negative rty *)


  | _ ->
    M.ret `Positive

let rec tac_rst tac ty =
  let rec go sys ty =
    match Tm.unleash ty with
    | Tm.Rst rst ->
      go (rst.sys @ sys) rst.ty
    | _ ->
      begin
        match sys with
        | [] -> tac ty
        | _ ->
          normalize_ty ty >>= fun ty ->
          push_restriction sys ty >>= function
          | `Positive ->
            tac ty >>=
            guess_restricted ty sys
          | `Negative rty ->
            tac rty
      end
  in go [] ty


let tac_wrap_nf tac ty =
  try tac ty
  with
  | ChkMatch ->
    normalize_ty ty >>= tac_rst tac



let tac_let name itac ctac =
  fun ty ->
    itac >>= fun (let_ty, let_tm) ->
    let singleton_ty =
      let face = Tm.make Tm.Dim0, Tm.make Tm.Dim0, Some let_tm in
      Tm.make @@ Tm.Rst {ty = let_ty; sys = [face]}
    in
    let x = Name.named @@ Some name in
    M.in_scope x (`P singleton_ty) (ctac ty) >>= fun bdyx ->
    let inf = Tm.Down {ty = let_ty; tm = let_tm}, Emp in
    M.ret @@ Tm.make @@ Tm.Let (inf, Tm.bind x bdyx)


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
        let ty, sys = Tm.unbind_ext_with (Bwd.to_list xs) ebnd in
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
    Format.eprintf "Shit: %a@." Tm.pp0 ty;
    failwith "Expected datatype"

module MonadUtil = Monad.Util (ElabMonad)
open MonadUtil

let tac_elim ~tac_mot ~tac_scrut ~clauses : chk_tac =
  fun ty ->
    tac_scrut >>= fun (data_ty, scrut) ->
    let univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kind.Pre in
    let mot_ty = Tm.pi None data_ty univ in
    begin
      match tac_mot with
      | None ->
        let is_dependent =
          match Tm.unleash scrut with
          | Tm.Up (Tm.Var {name; _}, _) when Occurs.Set.mem name @@ Tm.free `Vars ty -> true
          | _ -> false
        in
        if is_dependent then
          M.lift @@ U.push_hole `Flex Emp mot_ty >>= fun (mothd, motsp) ->
          let mot arg = Tm.up (mothd, motsp #< (Tm.FunApp arg)) in
          M.lift @@ C.active @@ Problem.eqn ~ty0:univ ~ty1:univ ~tm0:ty ~tm1:(mot scrut) >>
          M.unify >>
          M.ret mot
        else
          M.ret (fun _ -> ty)
      | Some tac_mot ->
        tac_mot mot_ty >>= fun mot ->
        let fmot arg = Tm.up (Tm.Down {ty = mot_ty; tm = mot}, Emp #< (Tm.FunApp arg)) in
        M.ret fmot
    end >>= fun mot ->

    let dlbl = unleash_data data_ty in

    begin
      M.lift C.base_cx <<@> fun cx ->
        let sign = Cx.globals cx in
        GlobalEnv.lookup_datatype dlbl sign
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
            List.map (fun (plbl, _) -> ESig.PVar plbl) constr.params
            @ List.mapi (fun i _ -> let x = "x" ^ string_of_int i in ESig.PIndVar (x, x ^ "/ih")) constr.args
          in
          lbl, pbinds, fun ty ->
            M.lift C.ask >>= fun psi ->
            M.lift @@ U.push_hole `Rigid psi ty >>= fun tm ->
            M.emit @@ M.UserHole {name = Some lbl; ty; tele = psi; tm = Tm.up tm} >>
            M.ret @@ Tm.up tm
      in
      List.map (fun (lbl, _) -> find_clause lbl) desc
    in

    begin
      M.lift C.base_cx <<@> fun cx ->
        Cx.evaluator cx, Cx.quoter cx
    end >>= fun ((module V), (module Q)) ->

    let refine_clause (clbl, pbinds, (clause_tac : chk_tac)) =
      let open Desc in
      let constr = lookup_constr clbl desc in
      let rec go psi env tms pbinds ps args =
        match pbinds, ps, args with
        | ESig.PVar nm :: pbinds, (_plbl, pty) :: ps, _ ->
          let x = Name.named @@ Some nm in
          let vty = V.eval env pty in
          let tty = Q.quote_ty Quote.Env.emp vty in
          let x_el = V.reflect vty (D.Var {name = x; twin = `Only; ushift = 0}) [] in
          let x_tm = Tm.up @@ Tm.var x in
          let env' = D.Env.push (D.Val x_el) env in
          go (psi #< (x, `P tty)) env' (tms #< x_tm) pbinds ps args

        | ESig.PVar nm :: pbinds, [], (_, Self) :: args ->
          let x = Name.named @@ Some nm in
          let x_ih = Name.fresh () in
          let x_tm = Tm.up @@ Tm.var x in
          let ih_ty = mot x_tm in
          go (psi #< (x, `P data_ty) #< (x_ih, `P ih_ty)) env (tms #< x_tm) pbinds [] args

        | ESig.PIndVar (nm, nm_ih) :: pbinds, [], (_, Self) :: args ->
          let x = Name.named @@ Some nm in
          let x_ih = Name.named @@ Some nm_ih in
          let x_tm = Tm.up @@ Tm.var x in
          let ih_ty = mot x_tm in
          go (psi #< (x, `P data_ty) #< (x_ih, `P ih_ty)) env (tms #< x_tm) pbinds [] args

        | _, [], [] ->
          psi, Bwd.to_list tms

        | _ ->
          failwith "refine_clause"
      in
      let psi, tms = go Emp D.Env.emp Emp pbinds constr.params constr.args in
      let intro = Tm.make @@ Tm.Intro (clbl, tms) in
      let clause_ty = mot intro in
      begin
        M.in_scopes (Bwd.to_list psi) @@
        clause_tac clause_ty <<@> Tm.bindn (Bwd.map fst psi)
      end >>= fun bdy ->
      M.ret (clbl, bdy)
    in

    traverse (fun x -> x) @@ List.map refine_clause clauses >>= fun tclauses ->

    let hd = Tm.Down {ty = data_ty; tm = scrut} in
    let bmot =
      let x = Name.fresh () in
      Tm.bind x @@ mot @@ Tm.up @@ Tm.var x
    in
    let frm = Tm.Elim {dlbl; mot = bmot; clauses = tclauses} in
    M.ret @@ Tm.up (hd, Emp #< frm)

let tac_s1_elim ~tac_mot ~tac_scrut ~tac_bcase ~tac_lcase:(nm_lcase, tac_lcase) =
  fun ty ->
    let pre_univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kind.Pre in
    let kan_univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kind.Kan in
    let s1 = Tm.make @@ Tm.S1 in
    let mot_ty = Tm.pi None s1 kan_univ in
    let x_lcase = Name.named @@ Some nm_lcase in
    tac_scrut s1 >>= fun scrut ->
    begin
      match tac_mot with
      | None ->
        let is_dependent =
          match Tm.unleash scrut with
          | Tm.Up (Tm.Var {name; _}, _) when Occurs.Set.mem name @@ Tm.free `Vars ty -> true
          | _ -> false
        in
        if is_dependent then
          M.lift @@ U.push_hole `Flex Emp mot_ty >>= fun (mothd, motsp) ->
          let mot arg = Tm.up (mothd, motsp #< (Tm.FunApp arg)) in
          M.lift @@ C.active @@ Problem.eqn ~ty0:pre_univ ~ty1:pre_univ ~tm0:ty ~tm1:(mot scrut) >>
          M.unify >>
          M.ret mot
        else
          M.ret (fun _ -> ty)
      | Some tac_mot ->
        tac_mot mot_ty >>= fun mot ->
        let fmot arg = Tm.up (Tm.Down {ty = mot_ty; tm = mot}, Emp #< (Tm.FunApp arg)) in
        M.ret fmot
    end >>= fun mot ->

    let mot_base = mot @@ Tm.make Tm.Base in

    tac_bcase mot_base >>= fun bcase ->

    let mot_loop = mot @@ Tm.make @@ Tm.Loop (Tm.up (Tm.var x_lcase)) in

    M.in_scope x_lcase `I begin
      tac_lcase mot_loop >>= fun tm ->
      M.ret @@ Tm.bind x_lcase tm
    end >>= fun lcase ->

    let hd = Tm.Down {ty = s1; tm = scrut} in
    let bmot =
      let x = Name.fresh () in
      Tm.bind x @@ mot @@ Tm.up @@ Tm.var x
    in
    let frm = Tm.S1Rec {mot = bmot; bcase; lcase} in
    M.ret @@ Tm.up (hd, Emp #< frm)

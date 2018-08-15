open RedBasis
open RedTT_Core
open Dev open Bwd open BwdNotation

module D = Domain
module B = Desc.Boundary

module M =
struct
  include ElabMonad
  module Util = Monad.Util(ElabMonad)
end

module C = Contextual
module U = Unify
module Notation = Monad.Notation (M)
open Notation

type sys = (tm, tm) Tm.system
type goal = {ty : ty; sys : sys}
type chk_tac = goal -> tm M.m
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


let guess_restricted tm goal =
  let ty = goal.ty in
  let sys = goal.sys in
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

let bind_in_scope tm =
  M.lift C.ask <<@> fun psi ->
    let go (x, param) =
      match param with
      | `P _ -> [x]
      | `Def _ -> [x]
      | `I -> [x]
      | `SelfArg _ -> [x]
      | `Tick -> [x]
      | `Tw _ -> []
      | _ -> []
    in
    let xs = Bwd.flat_map go psi in
    let Tm.NB (_, tm) = Tm.bindn xs tm in
    tm

let tac_wrap_nf tac goal =
  try tac goal
  with
  | ChkMatch ->
    normalize_ty goal.ty >>= fun ty ->
    tac {ty; sys = goal.sys}


let tac_let name itac ctac =
  fun goal ->
    itac >>= fun (let_ty, let_tm) ->
    let x = Name.named @@ Some name in
    M.in_scope x (`Def (let_ty, let_tm)) (ctac goal) >>= fun bdyx ->
    M.ret @@ Tm.make @@ Tm.Let (Tm.ann ~ty:let_ty ~tm:let_tm, Tm.bind x bdyx)


let flip f x y = f y x

let rec tac_lambda names tac goal =
  match Tm.unleash goal.ty with
  | Tm.Pi (dom, cod) ->
    begin
      match names with
      | [] -> tac goal
      | name :: names ->
        let x = Name.named @@ Some name in
        let codx = Tm.unbind_with (Tm.var x) cod in
        let sysx =
          flip List.map goal.sys @@ fun (r, r', otm) ->
          r, r', flip Option.map otm @@ fun tm ->
          Tm.up @@ Tm.ann ~ty:goal.ty ~tm @< Tm.FunApp (Tm.up @@ Tm.var x)
        in
        M.in_scope x (`P dom) begin
          tac_wrap_nf (tac_lambda names tac) {ty = codx; sys = sysx}
        end >>= fun bdyx ->
        M.ret @@ Tm.make @@ Tm.Lam (Tm.bind x bdyx)
    end

  | Tm.Later cod ->
    begin
      match names with
      | [] -> tac goal
      | name :: names ->
        let x = Name.named @@ Some name in
        let codx = Tm.unbind_with (Tm.var x) cod in
        let sysx =
          flip List.map goal.sys @@ fun (r, r', otm) ->
          r, r', flip Option.map otm @@ fun tm ->
          Tm.up @@ Tm.ann ~ty:goal.ty ~tm @< Tm.Prev (Tm.up @@ Tm.var x)
        in
        M.in_scope x `Tick begin
          tac_wrap_nf (tac_lambda names tac) {ty = codx; sys = sysx}
        end >>= fun bdyx ->
        M.ret @@ Tm.make @@ Tm.Next (Tm.bind x bdyx)
    end

  | Tm.Ext (Tm.NB (nms, _) as ebnd) ->
    begin
      match names with
      | [] -> tac goal
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
        let xs_fwd = Bwd.to_list xs in
        let xs_tms = List.map (fun x -> Tm.var x) xs_fwd in
        let tyxs, sysxs = Tm.unbind_ext_with xs_tms ebnd in
        let ps = List.map (fun x -> (x, `I)) xs_fwd in
        let sys'xs =
          flip List.map goal.sys @@ fun (r, r', otm) ->
          r, r', flip Option.map otm @@ fun tm ->
          Tm.up @@ Tm.ann ~ty:goal.ty ~tm @< Tm.ExtApp (List.map Tm.up xs_tms)
        in
        M.in_scopes ps begin
          tac' {ty = tyxs; sys = sysxs @ sys'xs}
        end >>= fun bdyxs ->
        let lam = Tm.make @@ Tm.ExtLam (Tm.bindn xs bdyxs) in
        M.ret lam
    end

  | _ ->
    begin
      match names with
      | [] -> tac goal
      | _ ->
        raise ChkMatch
    end

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
    tac_mot {ty = mot_ty; sys = []} >>= fun mot ->
    let motx =
      Tm.ann ~ty:(Tm.subst (Tm.shift 1) mot_ty) ~tm:(Tm.subst (Tm.shift 1) mot)
      @< Tm.FunApp (Tm.up @@ Tm.ix 0)
    in
    M.ret @@ Tm.B (None, Tm.up @@ motx)

let tac_elim ~loc ~tac_mot ~tac_scrut ~clauses : chk_tac =
  fun goal ->
    tac_scrut >>= fun (data_ty, scrut) ->
    normalize_ty data_ty >>= fun data_ty ->

    make_motive ~data_ty ~scrut ~tac_mot ~ty:goal.ty >>= fun bmot ->

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
    let eclauses =
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
          lbl, pbinds, fun goal ->
            M.lift C.ask >>= fun psi ->
            let rty = Tm.make @@ Tm.Rst {ty = goal.ty; sys = goal.sys} in
            M.lift @@ U.push_hole `Rigid psi rty  >>= fun tm ->
            M.emit loc @@ M.UserHole {name = Some lbl; ty = rty; tele = psi; tm = Tm.up tm} >>
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
      let rec go psi env (tms, cargs, rargs, ihs, rs) pbinds const_specs rec_specs dims =
        match pbinds, const_specs, rec_specs, dims with
        | ESig.PVar nm :: pbinds, (_plbl, pty) :: const_specs, _, _->
          let x = Name.named @@ Some nm in
          let vty = V.eval env pty in
          let tty = Q.quote_ty Quote.Env.emp vty in
          let x_el = V.reflect vty (D.Var {name = x; twin = `Only; ushift = 0}) [] in
          let x_tm = Tm.up @@ Tm.var x in
          let env' = D.Env.push (`Val x_el) env in
          go (psi #< (x, `P tty)) env' (tms #< x_tm, cargs #< x_el, rargs, ihs, rs) pbinds const_specs rec_specs dims

        | ESig.PVar nm :: pbinds, [], (_, Self) :: rec_specs, _ ->
          let x = Name.named @@ Some nm in
          let x_ih = Name.fresh () in
          let x_tm = Tm.up @@ Tm.var x in
          let x_el = V.reflect data_vty (D.Var {name = x; twin = `Only; ushift = 0}) [] in
          let ih_ty = mot x_tm in
          go (psi #< (x, `P data_ty) #< (x_ih, `P ih_ty)) env (tms #< x_tm, cargs, rargs #< x_el, ihs #< x_ih, rs) pbinds const_specs rec_specs dims

        | ESig.PIndVar (nm, nm_ih) :: pbinds, [], (_, Self) :: rec_specs, _ ->
          let x = Name.named @@ Some nm in
          let x_ih = Name.named @@ Some nm_ih in
          let x_tm = Tm.up @@ Tm.var x in
          let ih_ty = mot x_tm in
          let x_el = V.reflect data_vty (D.Var {name = x; twin = `Only; ushift = 0}) [] in
          go (psi #< (x, `P data_ty) #< (x_ih, `P ih_ty)) env (tms #< x_tm, cargs, rargs #< x_el, ihs #< x_ih, rs) pbinds const_specs rec_specs dims

        | ESig.PVar nm :: pbinds, [], [], _ :: dims ->
          let x = Name.named @@ Some nm in
          let x_tm = Tm.up @@ Tm.var x in
          let r = `Atom x in
          let env' = D.Env.push (`Dim r) env in
          go (psi #< (x, `I)) env' (tms #< x_tm, cargs, rargs, ihs, rs #< r) pbinds [] [] dims

        | _, [], [], [] ->
          psi, Bwd.to_list tms, Bwd.to_list cargs, Bwd.to_list rargs, ihs, Bwd.to_list rs

        | _ ->
          failwith "refine_clause"
      in

      let psi, tms, const_args, rec_args, ihs, rs = go Emp D.Env.emp (Emp, Emp, Emp, Emp, Emp) pbinds constr.const_specs constr.rec_specs constr.dim_specs in
      let sub = List.fold_left (fun sub (x,_) -> Tm.dot (Tm.var x) sub) (Tm.shift 0) (Bwd.to_list psi) in
      let intro = Tm.make @@ Tm.Intro (dlbl, clbl, tms) in
      let clause_ty = mot intro in

      M.in_scopes (Bwd.to_list psi) begin
        begin
          M.lift C.base_cx <<@> fun cx ->
            cx, Cx.evaluator cx, Cx.quoter cx
        end >>= fun (cx, (module V), (module Q)) ->

        let rec image_of_bterm phi =
          function
          | B.Intro intro as bterm ->
            let nbnd : ty Tm.nbnd = snd @@ List.find (fun (clbl, _) -> clbl = intro.clbl) earlier_clauses in
            let nclo = D.NClo {nbnd; rho = Cx.env cx} in
            let cargs = List.map (fun t -> `Val (Cx.eval cx @@ Tm.subst sub t)) intro.const_args in
            let rargs = List.map (fun bt -> `Val (image_of_bterm phi bt)) intro.rec_args in
            let dims = List.map (fun t -> `Dim (Cx.eval_dim cx @@ Tm.subst sub t)) intro.rs in
            let cells = cargs @ rargs @ dims in
            V.inst_nclo nclo cells
          | B.Var ix ->
            let ix' = ix - List.length rs in
            Cx.eval_cmd cx @@ Tm.var @@ Bwd.nth ihs ix'
        in

        let image_of_bface (tr, tr', btm) =
          let env = Cx.env cx in
          let r = V.eval_dim env @@ Tm.subst sub tr in
          let r' = V.eval_dim env @@ Tm.subst sub tr' in
          D.ValFace.make I.idn r r' @@ fun phi ->
          image_of_bterm phi btm
        in

        (* What is the image of the boundary in the current fiber of the motive? *)
        let tsys =
          let val_sys = List.map image_of_bface constr.boundary in
          let vty = Cx.eval cx clause_ty in
          Q.quote_val_sys (Cx.qenv cx) vty val_sys
        in

        (* We run the clause tactic with the goal type restricted by the boundary above *)
        clause_tac {ty = clause_ty; sys = tsys} <<@> fun bdy ->
          clbl, Tm.bindn (Bwd.map fst psi) bdy
      end
    in

    M.Util.fold_left (fun acc clause -> refine_clause acc clause <<@> fun cl -> cl :: acc) [] eclauses >>= fun clauses ->
    M.ret @@ Tm.up @@ Tm.ann ~ty:data_ty ~tm:scrut @< Tm.Elim {dlbl; mot = bmot; clauses}

let rec hope goal =
  let rst = Tm.make @@ Tm.Rst {ty = goal.ty; sys = goal.sys} in
  let rec try_system sys =
    match sys with
    | [] ->
      M.lift C.ask >>= fun psi ->
      let rty = Tm.make @@ Tm.Rst {ty = goal.ty; sys = goal.sys} in
      M.lift @@ U.push_hole `Flex psi rty <<@> Tm.up
    | (r, r', Some tm) :: sys ->
      begin
        M.lift @@ C.check ~ty:rst tm >>=
        function
        | `Ok ->
          M.ret tm
        | _ ->
          try_system sys
      end
    | _ :: sys ->
      try_system sys
  in
  try_system goal.sys

(* TODO: introduce sigma, etc. *)
let rec auto goal =
  normalize_ty goal.ty >>= fun ty ->
  let goal = {goal with ty} in
  match Tm.unleash ty with
  | Tm.Ext (Tm.NB (nms, _)) ->
    let nms' = Bwd.to_list @@ Bwd.map (function Some nm -> nm | None -> "_") nms in
    tac_lambda nms' auto goal

  | Tm.Pi (dom, Tm.B (nm, _)) ->
    let nms = [match nm with Some nm -> nm | None -> "_"] in
    tac_lambda nms auto goal

  | _ ->
    hope goal

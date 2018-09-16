open RedBasis
open RedTT_Core
open Dev open Bwd open BwdNotation

module D = Domain

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

let normalizing_goal tac goal =
  normalize_ty goal.ty >>= fun ty ->
  tac {goal with ty}

let rec tac_fix ftac goal =
  ftac (tac_fix ftac) goal

let match_goal tac =
  fun goal ->
    tac goal goal


let guess_restricted tm goal =
  let ty = goal.ty in
  let sys = goal.sys in
  M.lift @@ C.check ~ty ~sys tm >>= function
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
    M.lift @@ C.check ~ty ~sys tm >>= function
    | `Ok -> M.ret tm
    | `Exn exn ->
      raise exn

exception ChkMatch

let bind_in_scope_ psi tm =
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
  let Tm.NB (_, tm) = Tm.bindn xs tm in
  tm

let bind_in_scope tm =
  M.lift C.ask <<@> fun psi -> bind_in_scope_ psi tm


let bind_sys_in_scope sys =
  M.lift C.ask <<@> fun psi ->
    Tm.map_tm_sys (bind_in_scope_ psi) sys

let tac_wrap_nf tac goal =
  try tac goal
  with
  | ChkMatch ->
    normalize_ty goal.ty >>= fun ty ->
    tac {ty; sys = goal.sys}


let tac_let x itac ctac =
  fun goal ->
    itac >>= fun (let_ty, let_tm) ->
    M.in_scope x (`Def (let_ty, let_tm)) (ctac goal) >>= fun bdyx ->
    M.ret @@ Tm.make @@ Tm.Let (Tm.ann ~ty:let_ty ~tm:let_tm, Tm.bind x bdyx)


let flip f x y = f y x

let rec tac_lambda xs tac goal =
  match Tm.unleash goal.ty with
  | Tm.Pi (dom, cod) ->
    begin
      match xs with
      | [] -> tac goal
      | x :: xs ->
        let codx = Tm.unbind_with (Tm.var x) cod in
        let sysx =
          flip List.map goal.sys @@ fun (r, r', otm) ->
          r, r', flip Option.map otm @@ fun tm ->
          Tm.up @@ Tm.ann ~ty:goal.ty ~tm @< Tm.FunApp (Tm.up @@ Tm.var x)
        in
        M.in_scope x (`P dom) begin
          tac_wrap_nf (tac_lambda xs tac) {ty = codx; sys = sysx}
        end >>= fun bdyx ->
        M.ret @@ Tm.make @@ Tm.Lam (Tm.bind x bdyx)
    end

  | Tm.Later cod ->
    begin
      match xs with
      | [] -> tac goal
      | x :: xs ->
        let codx = Tm.unbind_with (Tm.var x) cod in
        let sysx =
          flip List.map goal.sys @@ fun (r, r', otm) ->
          r, r', flip Option.map otm @@ fun tm ->
          Tm.up @@ Tm.ann ~ty:goal.ty ~tm @< Tm.Prev (Tm.up @@ Tm.var x)
        in
        M.in_scope x `Tick begin
          tac_wrap_nf (tac_lambda xs tac) {ty = codx; sys = sysx}
        end >>= fun bdyx ->
        M.ret @@ Tm.make @@ Tm.Next (Tm.bind x bdyx)
    end

  | Tm.Ext (Tm.NB (nms, _) as ebnd) ->
    begin
      match xs with
      | [] -> tac goal
      | _ ->
        let rec bite xs lxs rxs =
          match xs, rxs with
          | Emp, _ -> lxs, tac_wrap_nf (tac_lambda rxs tac)
          | Snoc (nms, _), x :: rxs ->
            bite nms (lxs #< x) rxs
          | _ -> failwith "Elab: incorrect number of binders when refining extension type"
        in
        let xs, tac' = bite nms Emp xs in
        let xs_fwd = Bwd.to_list xs in
        let xs_tms = List.map (fun x -> Tm.var x) xs_fwd in
        let tyxs, sysxs = Tm.unbind_ext_with xs_tms ebnd in
        let ps =
          match xs_fwd with
          | [] ->
            [(Name.fresh (), `NullaryExt)]
          | _ ->
            List.map (fun x -> (x, `I)) xs_fwd
        in
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
      match xs with
      | [] -> tac goal
      | _ ->
        raise ChkMatch
    end

let tac_pair tac0 tac1 : chk_tac =
  fun goal ->
    match Tm.unleash goal.ty with
    | Tm.Sg (dom, cod) ->
      let sys0 =
        flip List.map goal.sys @@ fun (r, r', otm) ->
        r, r', flip Option.map otm @@ fun tm ->
        Tm.up @@ Tm.ann ~ty:goal.ty ~tm @< Tm.Car
      in
      let sys1 =
        flip List.map goal.sys @@ fun (r, r', otm) ->
        r, r', flip Option.map otm @@ fun tm ->
        Tm.up @@ Tm.ann ~ty:goal.ty ~tm @< Tm.Cdr
      in
      tac0 {ty = dom; sys = sys0} >>= fun tm0 ->
      let cmd0 = Tm.ann ~ty:dom ~tm:tm0 in
      let cod' = Tm.make @@ Tm.Let (cmd0, cod) in
      tac1 {ty = cod'; sys = sys1} >>= fun tm1 ->
      M.ret @@ Tm.cons tm0 tm1

    | _ ->
      raise ChkMatch

let unleash_data ty =
  match Tm.unleash ty with
  | Tm.Data dlbl -> dlbl
  | _ ->
    Format.eprintf "Dang: %a@." Tm.pp0 ty;
    failwith "Expected datatype"

let inspect_goal ~loc ~name : goal -> unit M.m =
  fun goal ->
    M.lift C.ask >>= fun psi ->
    let rty = Tm.refine_ty goal.ty goal.sys in
    begin
      if name = Some "_" then M.ret () else
        M.emit loc @@ M.UserHole {name; ty = rty; tele = psi}
    end

let tac_hole ~loc ~name : chk_tac =
  fun goal ->
    inspect_goal ~loc ~name goal >>
    M.lift C.ask >>= fun psi ->
    let rty = Tm.refine_ty goal.ty goal.sys in
    M.lift @@ U.push_hole `Rigid psi rty >>= fun cmd ->
    M.ret @@ Tm.up @@ Tm.refine_force cmd

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

let lookup_datatype dlbl =
  M.lift C.base_cx <<@> fun cx ->
    GlobalEnv.lookup_datatype dlbl @@ Cx.globals cx

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

    lookup_datatype dlbl >>= fun desc ->

    (* Add holes for any missing clauses *)
    let eclauses =
      let find_clause lbl =
        try
          List.find (fun (lbl', _, _) -> lbl = lbl') clauses
        with
        | Not_found ->
          let constr = Desc.lookup_constr lbl desc in
          let pbinds =
            flip List.map constr.specs @@ function
            | nm, (`Const _ | `Dim) -> ESig.PVar nm
            | nm, `Rec _ -> ESig.PIndVar (nm, nm ^ "/ih")
          in
          lbl, pbinds, tac_hole ~loc ~name:(Some lbl)
      in
      List.map (fun (lbl, _) -> find_clause lbl) desc.constrs
    in

    (* TODO: factor this out into another tactic. *)
    let refine_clause earlier_clauses (clbl, pbinds, (clause_tac : chk_tac))  : (Desc.con_label * tm Tm.nbnd) M.m =

      let open Desc in
      let constr = lookup_constr clbl desc in

      begin
        M.lift C.base_cx <<@> fun cx ->
          let (module V) = Cx.evaluator cx in
          V.empty_env
      end >>= fun empty_env ->

      let rec prepare_clause (psi, tyenv, intro_args, env_only_ihs) pbinds specs =
        begin
          M.lift C.base_cx <<@> fun cx ->
            cx, Cx.evaluator cx, Cx.quoter cx
        end >>= fun (cx, (module V), (module Q)) ->
        match pbinds, specs with
        | ESig.PVar nm :: pbinds, (_, `Const ty) :: specs ->
          let x = Name.named @@ Some nm in
          let vty = V.eval tyenv ty in
          let x_tm = Tm.up @@ Tm.var x in
          let x_el = V.reflect vty (D.Var {name = x; twin = `Only; ushift = 0}) [] in
          let tty = Q.quote_ty Quote.Env.emp vty in
          let psi = psi #< (x, `P tty) in
          let tyenv = D.Env.snoc tyenv @@ `Val x_el in
          let env_only_ihs = D.Env.snoc env_only_ihs @@ `Val x_el in
          let intro_args = intro_args #< x_tm in
          M.in_scope x (`P tty) @@
          prepare_clause (psi, tyenv, intro_args, env_only_ihs) pbinds specs

        | ESig.PVar nm :: pbinds, (_, `Dim) :: specs ->
          let x = Name.named @@ Some nm in
          let x_tm = Tm.up @@ Tm.var x in
          let x_el = `Atom x in
          let psi = psi #< (x, `I) in
          let tyenv = D.Env.snoc tyenv @@ `Dim x_el in
          let env_only_ihs = D.Env.snoc env_only_ihs @@ `Dim x_el in
          let intro_args = intro_args #< x_tm in
          M.in_scope x `I @@
          prepare_clause (psi, tyenv, intro_args, env_only_ihs) pbinds specs

        | pat :: pbinds, (_, `Rec Desc.Self) :: specs ->
          let x, x_ih =
            match pat with
            | PVar nm ->
              Name.named @@ Some nm, Name.fresh ()
            | PIndVar (nm, nm_ih) ->
              Name.named @@ Some nm, Name.named @@ Some nm_ih
          in
          let vty = data_vty in
          let x_tm = Tm.up @@ Tm.var x in
          let x_el = V.reflect vty (D.Var {name = x; twin = `Only; ushift = 0}) [] in
          let tty = Q.quote_ty Quote.Env.emp vty in
          let ih_ty = mot x_tm in

          M.in_scope x (`P data_ty) begin
            M.lift C.base_cx >>= fun cx ->
            let ih_vty = Cx.eval cx ih_ty in

            let ih_el = V.reflect ih_vty (D.Var {name = x_ih; twin = `Only; ushift = 0}) [] in
            let psi = psi <>< [x, `P tty; x_ih, `P ih_ty] in
            let tyenv = D.Env.snoc tyenv @@ `Val x_el in
            let env_only_ihs = D.Env.snoc env_only_ihs @@ `Val ih_el in
            let intro_args = intro_args #< x_tm in
            M.in_scope x_ih (`P ih_ty) @@
            prepare_clause (psi, tyenv, intro_args, env_only_ihs) pbinds specs
          end

        | [], [] ->
          M.ret (Bwd.to_list psi, tyenv, Bwd.to_list intro_args, env_only_ihs)

        | _ ->
          failwith "prepare_clause: mismatch"
      in

      prepare_clause (Emp, empty_env, Emp, empty_env) pbinds constr.specs >>= fun (psi, env, intro_args, env_only_ihs) ->

      let intro = Tm.make @@ Tm.Intro (dlbl, clbl, intro_args) in
      let clause_ty = mot intro in

      M.lift C.base_cx >>= fun outer_cx ->

      M.in_scopes psi begin
        begin
          M.lift C.base_cx <<@> fun cx ->
            cx, Cx.evaluator cx, Cx.quoter cx
        end >>= fun (cx, (module V), (module Q)) ->

        let rec image_of_bterm phi tm =
          let benv = env in
          match Tm.unleash tm with
          | Tm.Intro (_, clbl, args) ->
            let constr = Desc.lookup_constr clbl desc in
            let nbnd = snd @@ List.find (fun (clbl', _) -> clbl = clbl') earlier_clauses in
            let nclo : D.nclo = D.NClo.act phi @@ D.NClo {rho = Cx.env outer_cx; nbnd} in
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
                Format.eprintf "Tm: %a@." Tm.pp0 tm;
                failwith "image_of_bterm"
            in
            V.inst_nclo nclo @@ go constr.specs args
          | _ ->
            D.Value.act phi @@ V.eval env_only_ihs tm

        in

        let image_of_bface (tr, tr', otm) =
          let r = V.eval_dim env tr in
          let r' = V.eval_dim env tr' in
          D.ValFace.make I.idn r r' @@ fun phi ->
          let tm = Option.get_exn otm in
          image_of_bterm phi tm
        in

        (* What is the image of the boundary in the current fiber of the motive? *)
        let tsys =
          let val_sys = List.map image_of_bface constr.boundary in
          let vty = Cx.eval cx clause_ty in
          Q.quote_val_sys (Cx.qenv cx) vty val_sys
        in

        (* We run the clause tactic with the goal type restricted by the boundary above *)
        clause_tac {ty = clause_ty; sys = tsys} <<@> fun bdy ->
          clbl, Tm.bindn (Bwd.map fst @@ Bwd.from_list psi) bdy
      end
    in

    M.Util.fold_left (fun acc clause -> refine_clause acc clause <<@> fun cl -> cl :: acc) [] eclauses >>= fun clauses ->
    M.ret @@ Tm.up @@ Tm.ann ~ty:data_ty ~tm:scrut @< Tm.Elim {dlbl; mot = bmot; clauses}

let rec tac_hope goal =
  let rec try_system sys =
    match sys with
    | [] ->
      M.lift C.ask >>= fun psi ->
      let rty = Tm.refine_ty goal.ty goal.sys in
      M.lift @@ U.push_hole `Flex psi rty <<@> fun cmd -> Tm.up @@ Tm.refine_force cmd
    | (r, r', Some tm) :: sys ->
      begin
        M.lift @@ C.check ~ty:goal.ty ~sys:goal.sys tm >>=
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

let tac_guess tac : chk_tac =
  fun goal ->
    tac {goal with sys = []} >>= fun tm ->
    let rty = Tm.refine_ty goal.ty goal.sys in
    let rty0 = Tm.refine_ty goal.ty [] in
    M.lift C.ask >>= fun psi ->
    M.lift @@ U.push_guess psi ~ty0:rty ~ty1:rty0 (Tm.refine_thunk tm) <<@> fun tm ->
        Tm.up @@ Tm.refine_force @@ Tm.ann ~ty:rty ~tm

let tac_refl =
  tac_fix @@ fun tac_refl ->
  normalizing_goal @@ match_goal @@ fun goal ->
  match Tm.unleash goal.ty with
  | Tm.Ext (Tm.NB (nms, _)) ->
    let xs = Bwd.to_list @@ Bwd.map Name.named nms in
    tac_lambda xs tac_refl

  | Tm.Pi (dom, Tm.B (nm, _)) ->
    let xs = [Name.named nm] in
    tac_lambda xs tac_refl

  | Tm.Sg (_, _) ->
    tac_pair tac_refl tac_refl

  | _ ->
    tac_hope

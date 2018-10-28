open RedBasis
open RedTT_Core
open Dev open Bwd open BwdNotation

module D = NewDomain

module M =
struct
  include Contextual
  module Util = Monad.Util(Contextual)
end

module C = Contextual
module Cx = NewCx
module U = Unify
module Ty = NewTyping
module Q = NewQuote

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

let unify =
  M.go_to_top >>
  M.local (fun _ -> Emp) U.ambulando

let normalize_ty ty =
  let now0 = Unix.gettimeofday () in
  C.base_cx >>= fun cx ->
  let vty = Ty.eval cx ty in
  let ty = Ty.quote_ty cx vty in
  let now1 = Unix.gettimeofday () in
  normalization_clock := !normalization_clock +. (now1 -. now0);
  M.ret ty

let name_of =
  function
  | `User a -> Name.named @@ Some a
  | `Gen x -> x


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
  C.check ~ty ~sys tm >>= function
  | `Ok -> M.ret tm
  | _ ->
    let rec go =
      function
      | [] ->
        M.ret ()
      | (r, r', tm') :: sys ->
        begin
          M.under_restriction r r' @@
          C.active @@ Unify {ty0 = ty; ty1 = ty; tm0 = tm; tm1 = tm'}
        end >>
        go sys
    in
    go sys >>
    unify >>
    C.check ~ty ~sys tm >>= function
    | `Ok -> M.ret tm
    | `Exn exn ->
      raise exn

exception ChkMatch

let tac_wrap_nf tac goal =
  try tac goal
  with
  | ChkMatch ->
    normalize_ty goal.ty >>= fun ty ->
    tac {ty; sys = goal.sys}

let tac_of_cmd cmd =
  C.base_cx >>= fun cx ->
  let vty = Ty.infer_ty cx cmd in
  let ty = Ty.quote_ty cx vty in
  M.ret (ty, Tm.up cmd)


let tac_let x itac ctac =
  fun goal ->
    itac >>= fun (let_ty, let_tm) ->
    M.in_scope x (`Def (let_ty, let_tm)) (ctac goal) >>= fun bdyx ->
    M.ret @@ Tm.make @@ Tm.Let (Tm.ann ~ty:let_ty ~tm:let_tm, Tm.bind x bdyx)



let tac_pair tac0 tac1 : chk_tac =
  fun goal ->
    match Tm.unleash goal.ty with
    | Tm.Sg (dom, cod) ->
      let sys0 =
        ListUtil.foreach goal.sys @@ fun (r, r', tm) ->
        r, r', Tm.up @@ Tm.ann ~ty:goal.ty ~tm @< Tm.Fst
      in
      let sys1 =
        ListUtil.foreach goal.sys @@ fun (r, r', tm) ->
        r, r', Tm.up @@ Tm.ann ~ty:goal.ty ~tm @< Tm.Snd
      in
      tac0 {ty = dom; sys = sys0} >>= fun tm0 ->
      let cmd0 = Tm.ann ~ty:dom ~tm:tm0 in
      let cod' = Tm.make @@ Tm.Let (cmd0, cod) in
      tac1 {ty = cod'; sys = sys1} >>= fun tm1 ->
      M.ret @@ Tm.cons tm0 tm1

    (* FIXME this is totally wrong. we should consult the context to determine
     * whether r = 0/1 or not. Without really checking it, vin could be given
     * the wrong parameters from a non-rigid V type. *)
    | Tm.V {r; ty0; ty1; equiv} ->
      let () = match Tm.unleash r with
        | Tm.Up (Tm.Var _, []) -> ()
        | _ -> failwith "V is not rigid when applying the tac_pair tactic."
      in
      M.under_restriction r (Tm.make Tm.Dim0) @@
      tac0 {ty = ty0; sys = goal.sys} <<@>
      begin
        function
        | Some tm0 -> tm0
        | None -> failwith "V is not rigid when applying the tac_pair tactic."
      end
      >>= fun tm0 ->
      tac1 {ty = ty1; sys = goal.sys} >>= fun tm1 ->
      M.ret @@ Tm.make @@ Tm.VIn {r; tm0; tm1}

    | _ ->
      raise ChkMatch

let unleash_data ty =
  match Tm.unleash ty with
  | Tm.Data info -> info.lbl, info.params
  | _ ->
    failwith "Expected datatype"

let normalize_param p =
  let module Notation = Monad.Notation (C) in
  let open Notation in

  C.base_cx >>= fun cx ->
  let normalize_ty ty =
    let vty = Ty.eval cx ty in
    Ty.quote_ty cx vty
  in
  match p with
  | `P ty ->
    C.ret @@ `P (normalize_ty ty)
  | `Def (ty, tm) ->
    let vty = Ty.eval cx ty in
    let ty' = Ty.quote_ty cx vty in
    let el = Ty.eval cx tm in
    let tm' = Ty.quote cx vty el in
    C.ret @@ `Def (ty', tm')
  | `Tw (ty0, ty1) ->
    C.ret @@ `Tw (normalize_ty ty0, normalize_ty ty1)
  | (`I | `NullaryExt) as p ->
    C.ret p
  | `R (r0, r1) ->
    C.ret @@ `R (r0, r1)

let rec normalize_tele =
  let module Notation = Monad.Notation (C) in
  let open Notation in
  function
  | [] -> C.ret []
  | (x, p) :: tele ->
    normalize_param p >>= fun p ->
    C.in_scope x p (normalize_tele tele) >>= fun psi ->
    C.ret @@ (x,p) :: psi


let inspect_goal ~loc ~name : goal -> unit M.m =
  fun goal ->
    C.ask >>= fun tele ->
    let ty = Tm.refine_ty goal.ty goal.sys in
    begin
      if name = Some "_" then M.ret () else
        C.bind C.base_cx @@ fun cx ->
        C.bind (normalize_tele @@ Bwd.to_list tele) @@ fun tele ->
        let vty = Ty.eval cx ty in
        let ty = Ty.quote_ty cx vty in

        let pp_restriction fmt =
          let pp_bdy fmt tm = Tm.pp0 fmt tm in
          let pp_face fmt (r, r', tm) =
            Format.fprintf fmt "%a = %a %a @[%a@]"
              Tm.pp0 r
              Tm.pp0 r'
              Uuseg_string.pp_utf_8 "⇒"
              pp_bdy tm
          in
          Format.pp_print_list ~pp_sep:Format.pp_print_cut pp_face fmt
        in

        let pp_restricted_ty fmt (ty, sys) =
          match sys with
          | [] -> Tm.pp0 fmt ty
          | _ ->
            Format.fprintf fmt "%a@,@,with the following faces:@,@,   @[<v>%a@]"
              Tm.pp0 ty
              pp_restriction sys
        in

        let ty, sys =
          match Tm.unleash ty with
          | Tm.Ext (Tm.NB (Emp, (ty, sys))) ->
            ty, sys
          | _ ->
            ty, []
        in
        let pp fmt () =
          Format.fprintf fmt "@[<v>?%s:@; @[<v>%a@]@,@[<v>%a %a@]@]"
            (match name with Some name -> name | None -> "Hole")
            Dev.pp_params (Bwd.from_list tele)
            Uuseg_string.pp_utf_8 "⊢"
            pp_restricted_ty (ty, sys)
        in
        Log.pp_message ~loc ~lvl:`Info pp Format.std_formatter ();
        C.ret ()
        (* M.emit loc @@ M.UserHole {name; ty = rty; tele = psi} *)
    end

let tac_hole ~loc ~name : chk_tac =
  fun goal ->
    inspect_goal ~loc ~name goal >>
    C.ask >>= fun psi ->
    let rty = Tm.refine_ty goal.ty goal.sys in
    U.push_hole `Rigid psi rty >>= fun cmd ->
    M.ret @@ Tm.up @@ Tm.refine_force cmd

let guess_motive scrut ty =
  match Tm.unleash scrut with
  | Tm.Up (Tm.Var var, []) ->
    M.ret @@ Tm.bind var.name ty
  | _ ->
    M.ret @@ Tm.bind (Name.fresh ()) ty

let lookup_datatype dlbl =
  C.base_cx <<@> fun cx ->
    GlobalEnv.lookup_datatype (Cx.genv cx) dlbl

let make_motive ~data_ty ~tac_mot ~scrut ~ty =
  match tac_mot, ty with
  | None, Some ty ->
    guess_motive scrut ty
  | Some tac_mot, _ ->
    let univ = Tm.univ ~lvl:`Omega ~kind:`Pre in
    let mot_ty = Tm.pi None data_ty univ in
    tac_mot {ty = mot_ty; sys = []} >>= fun mot ->
    let motx =
      Tm.ann ~ty:(Tm.subst (Tm.shift 1) mot_ty) ~tm:(Tm.subst (Tm.shift 1) mot)
      @< Tm.FunApp (Tm.up @@ Tm.ix 0)
    in
    M.ret @@ Tm.B (None, Tm.up @@ motx)
  | _ -> failwith "make_motive"


let rec tac_lambda (ps : ML.einvpat list) tac goal =
  match Tm.unleash goal.ty with
  | Tm.Pi (dom, cod) ->
    begin
      match ps with
      | [] -> tac goal
      | p :: ps ->
        let x, p =
          match p with
          | `Var nm -> let x = name_of nm in x, `Var (`Gen x)
          | _ -> Name.fresh (), p
        in

        let codx = Tm.unbind_with (Tm.var x) cod in
        let sysx =
          ListUtil.foreach goal.sys @@ fun (r, r', tm) ->
          r, r', Tm.up @@ Tm.ann ~ty:goal.ty ~tm @< Tm.FunApp (Tm.up @@ Tm.var x)
        in
        M.in_scope x (`P dom) begin
          let tac : chk_tac =
            tac_inversion ~loc:None ~tac_scrut:(tac_of_cmd @@ Tm.var x) p @@
            tac_wrap_nf (tac_lambda ps tac)
          in
          tac {ty = codx; sys = sysx}
        end >>= fun bdyx ->
        M.ret @@ Tm.make @@ Tm.Lam (Tm.bind x bdyx)
    end

  | Tm.Ext (Tm.NB (nms, _) as ebnd) ->
    begin
      match ps with
      | [] -> tac goal
      | _ ->
        let rec bite xs lxs rps =
          match xs, rps with
          | Emp, _ -> lxs, tac_wrap_nf (tac_lambda rps tac)
          | Snoc (nms, _), `Var x :: rps ->
            bite nms (lxs #< (name_of x)) rps
          | _ -> failwith "Elab: incorrect number of binders when refining extension type"
        in
        let xs, tac' = bite nms Emp ps in
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
          ListUtil.foreach goal.sys @@ fun (r, r', tm) ->
          r, r', Tm.up @@ Tm.ann ~ty:goal.ty ~tm @< Tm.ExtApp (List.map Tm.up xs_tms)
        in
        M.in_scopes ps begin
          tac' {ty = tyxs; sys = sysxs @ sys'xs}
        end >>= fun bdyxs ->
        let lam = Tm.make @@ Tm.ExtLam (Tm.bindn xs bdyxs) in
        M.ret lam
    end

  | _ ->
    begin
      match ps with
      | [] -> tac goal
      | _ ->
        raise ChkMatch
    end

and split_sigma ~tac_scrut (tac_body : tm Tm.cmd -> tm Tm.cmd -> chk_tac) : chk_tac =
  match_goal @@ fun goal ->
  let xfun = Name.fresh () in
  let x0 = Name.fresh () in
  let x1 = Name.fresh () in
  let tac_fun =
    tac_scrut >>= fun (sigma_ty, scrut) ->
    normalize_ty sigma_ty >>= fun sigma_ty ->
    match Tm.unleash sigma_ty with
    | Tm.Sg (dom, cod) ->
      guess_motive scrut goal.ty >>= fun bmot ->
      let pair = Tm.cons (Tm.up @@ Tm.var x0) (Tm.up @@ Tm.var x1) in
      let mot_x0x1 = Tm.unbind_with (Tm.ann ~ty:sigma_ty ~tm:pair) bmot in
      let codx0 = Tm.unbind_with (Tm.var x0) cod in
      let fun_ty = Tm.make @@ Tm.Pi (dom, Tm.bind x0 @@ Tm.make @@ Tm.Pi (codx0, Tm.bind x1 @@ mot_x0x1)) in
      tac_down ~ty:fun_ty @@ tac_lambda [`Var (`Gen x0); `Var (`Gen x1)] @@ tac_body (Tm.var x0) (Tm.var x1)
    | _ ->
      failwith "split_sigma"
  in
  let tac_bdy =
    fun _ ->
      tac_scrut >>= fun (scrut_ty, scrut_tm) ->
      let scrut_cmd = Tm.ann ~ty:scrut_ty ~tm:scrut_tm in
      let pi0 = Tm.up @@ scrut_cmd @< Tm.Fst in
      let pi1 = Tm.up @@ scrut_cmd @< Tm.Snd in
      M.ret @@ Tm.up @@ (Tm.var xfun @< Tm.FunApp pi0) @< Tm.FunApp pi1
  in
  tac_let xfun tac_fun tac_bdy


and tac_down ~ty (ctac : chk_tac) : inf_tac =
  ctac {ty; sys = []} >>= fun tm ->
  M.ret (ty, tm)

and tac_generalize ~tac_scrut tac_body : chk_tac =
  match_goal @@ fun goal ->
  let xfun = Name.fresh () in
  let tac_fun =
    tac_scrut >>= fun (ty_scrut, tm_scrut) ->
    guess_motive tm_scrut goal.ty >>= fun bmot ->
    let fun_ty = Tm.make @@ Tm.Pi (ty_scrut, bmot) in
    tac_down ~ty:fun_ty tac_body
  in
  let tac_bdy =
    fun _ ->
      tac_scrut >>= fun (scrut_ty, scrut_tm) ->
      M.ret @@ Tm.up @@ (Tm.var xfun @< Tm.FunApp scrut_tm)
  in
  tac_let xfun tac_fun tac_bdy

and tac_inversion ~loc ~tac_scrut (invpat : ML.einvpat) (body : chk_tac) : chk_tac =
  match_goal @@ fun goal ->
  match invpat with
  | `Var nm ->
    fun goal ->
      tac_scrut >>= fun (_, tm) ->
      let x = name_of nm in
      if tm = Tm.up (Tm.var x) then body goal else
        tac_let x tac_scrut body goal

  | `Wildcard ->
    tac_elim ~loc ~tac_mot:None ~tac_scrut ~clauses:[] ~default:(Some body)

  | `SplitAs (inv0, inv1) ->
    split_sigma ~tac_scrut @@ fun cmd0 cmd1 ->
    tac_inversion ~loc ~tac_scrut:(tac_of_cmd cmd0) inv0 @@
    tac_inversion ~loc ~tac_scrut:(tac_of_cmd cmd1) inv1 @@
    body

  | `Split ->
    split_sigma ~tac_scrut @@ fun cmd0 cmd1 ->
    tac_generalize ~tac_scrut:(tac_of_cmd cmd1) @@
    tac_generalize ~tac_scrut:(tac_of_cmd cmd0) @@
    body

  | `Bite inv ->
    split_sigma ~tac_scrut @@ fun cmd0 cmd1 ->
    tac_inversion ~loc ~tac_scrut:(tac_of_cmd cmd0) inv @@
    tac_generalize ~tac_scrut:(tac_of_cmd cmd1) @@
    body

and tac_inv_let p itac ctac =
  match p with
  | `Var nm ->
    let x = name_of nm in
    tac_let x itac ctac
  | `Wildcard ->
    tac_elim ~loc:None ~tac_mot:None ~tac_scrut:itac ~clauses:[] ~default:(Some ctac)
  | `SplitAs (inv0, inv1) ->
    let itac0 =
      itac >>= fun (ty, tm) ->
      tac_of_cmd @@ Tm.ann ~ty ~tm @< Tm.Fst
    in
    let itac1 =
      itac >>= fun (ty, tm) ->
      tac_of_cmd @@ Tm.ann ~ty ~tm @< Tm.Snd
    in
    tac_inv_let inv0 itac0 @@ tac_inv_let inv1 itac1 @@ ctac
  | _ ->
    failwith "tac_inv_let: not supported"

and tac_elim_inf ~loc ~tac_mot ~tac_scrut ~clauses ~default : inf_tac =
  tac_scrut >>= fun (data_ty, scrut) ->
  normalize_ty data_ty >>= fun data_ty ->

  make_motive ~data_ty ~scrut ~tac_mot:(Some tac_mot) ~ty:None >>= fun bmot ->
  let goal = {ty = Tm.unbind_with (Tm.ann ~ty:data_ty ~tm:scrut) bmot; sys = []} in
  tac_elim ~loc ~tac_mot:(Some tac_mot) ~tac_scrut ~clauses ~default goal >>= fun tm ->
  M.ret (goal.ty, tm)

and tac_elim ~loc ~tac_mot ~tac_scrut ~clauses ~default : chk_tac =
  fun goal ->
    tac_scrut >>= fun (data_ty, scrut) ->
    normalize_ty data_ty >>= fun data_ty ->

    make_motive ~data_ty ~scrut ~tac_mot ~ty:(Some goal.ty) >>= fun bmot ->

    let mot arg =
      let Tm.B (_, motx) = bmot in
      let arg' = Tm.ann ~ty:data_ty ~tm:arg in
      Tm.subst (Tm.dot arg' (Tm.shift 0)) motx
    in


    let dlbl, params = unleash_data data_ty in
    begin
      C.base_cx >>= fun cx ->
      let vparams = List.map (fun tm -> D.Cell.con @@ Ty.eval cx tm) params in
      M.ret (Ty.eval cx data_ty, vparams)
    end
    >>= fun (data_vty, vparams) ->

    lookup_datatype dlbl >>= fun desc ->

    let constrs = Desc.Body.instance params desc.body in

    (* Add holes for any missing clauses *)
    let eclauses =
      let find_clause lbl =
        try
          List.find (fun (lbl', _, _) -> lbl = lbl') clauses
        with
        | Not_found ->
          let constr = Desc.lookup_constr lbl constrs in
          let pbinds =
            ListUtil.foreach (Desc.Constr.specs constr) @@ function
            | Some nm, (`Const _ | `Dim) -> `Bind (`Var (`User nm))
            | Some nm, `Rec _ -> `BindIH (`Var (`User nm), `Var (`User (nm ^ "/ih")))
            | None, _ -> `Bind (`Var (`User "_"))
          in
          lbl, pbinds,
          match default with
          | None -> tac_hole ~loc ~name:(Some lbl)
          | Some tac -> tac
      in
      List.map (fun (lbl, _) -> find_clause lbl) constrs
    in

    (* TODO: factor this out into another tactic. *)
    let refine_clause earlier_clauses (clbl, pbinds, (clause_tac : chk_tac))  : (string * tm Tm.nbnd) M.m =

      let constr = Desc.lookup_constr clbl constrs in


      C.global_env >>= fun genv ->
      let empty_env = D.Env.init genv in
      let mot_clo = D.(Clo {env = empty_env; bnd = bmot}) in

      let rec prepare_clause (psi, tyenv, intro_args, env_only_ihs, kont_tac) pbinds specs =
        C.base_cx >>= fun cx ->
        let rel = Cx.rel cx in
        match pbinds, specs with
        | `Bind (`Var nm) :: pbinds, Desc.TCons (`Const ty, Tm.B (_, specs)) ->
          let x = name_of nm in
          let vty = D.Syn.eval rel tyenv ty in
          let x_tm = Tm.up @@ Tm.var x in
          let x_el = D.Neutroid.reflect_head rel (D.Val.make vty) (D.Var {name = x; twin = `Only; ushift = 0}) [] in
          let tty = Q.equate_tycon (Q.QEnv.init genv) rel vty vty in
          let psi = psi #< (x, `P tty) in
          let tyenv = D.Env.extend_cell tyenv @@ D.Cell.con x_el in
          let env_only_ihs = D.Env.extend_cell env_only_ihs @@ D.Cell.con x_el in
          let intro_args = intro_args #< x_tm in
          M.in_scope x (`P tty) @@
          prepare_clause (psi, tyenv, intro_args, env_only_ihs, kont_tac) pbinds specs

        | `Bind (`Var nm) :: pbinds, Desc.TCons (`Dim, Tm.B (_, specs)) ->
          let x = name_of nm in
          let x_tm = Tm.up @@ Tm.var x in
          let x_el = `Atom x in
          let psi = psi #< (x, `I) in
          let tyenv = D.Env.extend_cell tyenv @@ D.Cell.dim x_el in
          let env_only_ihs = D.Env.extend_cell env_only_ihs @@ D.Cell.dim x_el in
          let intro_args = intro_args #< x_tm in
          M.in_scope x `I @@
          prepare_clause (psi, tyenv, intro_args, env_only_ihs, kont_tac) pbinds specs

        | `BindIH (`Var nm, `Var nm_ih) :: pbinds, Desc.TCons (`Rec Desc.Self, Tm.B (_, specs)) ->
          let x = name_of nm in
          let x_ih = name_of nm_ih in
          let vty = Ty.eval cx data_ty in
          let x_tm = Tm.up @@ Tm.var x in
          let x_el = D.Neutroid.reflect_head rel (D.Val.make vty) (D.Var {name = x; twin = `Only; ushift = 0}) [] in
          let tty = Q.equate_tycon (Q.QEnv.init genv) rel vty vty in
          let ih_vty = D.Clo.inst rel mot_clo @@ D.Cell.con x_el in
          let ih_ty = Q.equate_tycon (Q.QEnv.init genv) rel ih_vty ih_vty in

          M.in_scope x (`P data_ty) begin
            C.base_cx >>= fun cx ->
            let ih_el = D.Neutroid.reflect_head rel (D.Val.make ih_vty) (D.Var {name = x_ih; twin = `Only; ushift = 0}) [] in
            let psi = psi <>< [x, `P tty; x_ih, `P ih_ty] in
            let tyenv = D.Env.extend_cell tyenv @@ D.Cell.con x_el in
            let env_only_ihs = D.Env.extend_cell env_only_ihs @@ D.Cell.con ih_el in
            let intro_args = intro_args #< x_tm in
            M.in_scope x_ih (`P ih_ty) @@
            prepare_clause (psi, tyenv, intro_args, env_only_ihs, kont_tac) pbinds specs
          end

        | `Bind p :: pbinds, (Desc.TCons (`Rec _, _) as specs) ->
          prepare_clause (psi, tyenv, intro_args, env_only_ihs, kont_tac) (`BindIH (p, `Var (`Gen (Name.fresh ()))) :: pbinds) specs

        | `Bind inv :: pbinds, (Desc.TCons (spec, _) as specs) ->
          let x = Name.fresh () in
          let kont_tac tac =
            kont_tac @@
            let vty =
              match spec with
              | `Const ty -> D.Syn.eval rel tyenv ty
              | `Rec Desc.Self -> data_vty
              | _ -> failwith "unexpected wildcard pattern"
            in

            let ty = Q.equate_tycon (Q.QEnv.init genv) rel vty vty in
            let tac_scrut = M.ret (ty, Tm.up @@ Tm.var x) in
            tac_inversion ~loc ~tac_scrut inv tac
          in
          prepare_clause (psi, tyenv, intro_args, env_only_ihs, kont_tac) (`Bind (`Var (`Gen x)) :: pbinds) specs

        | `BindIH (`Var y, inv) :: pbinds, (Desc.TCons (`Rec rspec, _) as specs) ->
          let x_ih = Name.fresh () in
          let kont_tac tac =
            kont_tac @@
            let ty = mot @@ Tm.up @@ Tm.var x_ih in
            let tac_scrut = M.ret (ty, Tm.up @@ Tm.var x_ih) in
            tac_inversion ~loc ~tac_scrut inv tac
          in
          prepare_clause (psi, tyenv, intro_args, env_only_ihs, kont_tac) (`BindIH (`Var y, `Var (`Gen x_ih)) :: pbinds) specs

        | `BindIH (inv, p) :: pbinds, (Desc.TCons (`Rec rspec, _) as specs) ->
          let x = Name.fresh () in
          let kont_tac tac =
            kont_tac @@
            let ty = data_ty in
            let tac_scrut = M.ret (ty, Tm.up @@ Tm.var x) in
            tac_inversion ~loc ~tac_scrut inv tac
          in
          prepare_clause (psi, tyenv, intro_args, env_only_ihs, kont_tac) (`BindIH (`Var (`Gen x), p) :: pbinds) specs

        | [], Desc.TNil _ ->
          M.ret (Bwd.to_list psi, tyenv, Bwd.to_list intro_args, env_only_ihs, kont_tac)

        | _ ->
          failwith "prepare_clause: mismatch"
      in

      let tyenv = D.Env.extend_cells empty_env vparams in
      prepare_clause (Emp, tyenv, Emp, empty_env, fun tac -> tac) pbinds constr >>= fun (psi, env, intro_args, env_only_ihs, kont_tac) ->

      let intro = Tm.make @@ Tm.Intro (dlbl, clbl, params, intro_args) in
      let clause_ty = mot intro in

      C.base_cx >>= fun outer_cx ->

      M.in_scopes psi begin
        C.base_cx >>= fun cx ->

        let rec image_of_bterm rel tm =
          let benv = env in
          match Tm.unleash tm with
          | Tm.Intro (_, clbl, _, args) ->
            let constr = Desc.lookup_constr clbl constrs in
            let bnd = snd @@ List.find (fun (clbl', _) -> clbl = clbl') earlier_clauses in
            let nclo : D.nclo = D.NClo {env = Cx.venv outer_cx; bnd} in
            let rec go specs tms =
              match specs, tms with
              | Desc.TCons (`Const _, Tm.B (_, specs)), tm :: tms ->
                D.Cell.con (D.Syn.eval rel benv tm) :: go specs tms
              | Desc.TCons (`Rec Desc.Self, Tm.B (_, specs)), tm :: tms ->
                D.Cell.con (D.Syn.eval rel benv tm) :: D.Cell.con (image_of_bterm rel tm) :: go specs tms
              | Desc.TCons (`Dim, Tm.B (_, specs)), tm :: tms ->
                D.Cell.dim (D.Syn.eval_dim benv tm) :: go specs tms
              | Desc.TNil _, [] ->
                []
              | _ ->
                failwith "image_of_bterm"
            in
            D.NClo.inst rel nclo @@ go constr args
          | _ ->
            D.Syn.eval rel env_only_ihs tm

        in

        let image_of_bface (tr, tr', tm) =
          let r = D.Syn.eval_dim env tr in
          let r' = D.Syn.eval_dim env tr' in
          let rel_rr' = NewRestriction.equate' r r' (Cx.rel cx) in
          r, r', D.LazyVal.make @@ image_of_bterm rel_rr' tm
        in

        (* What is the image of the boundary in the current fiber of the motive? *)
        let tsys =
          let val_sys = List.map image_of_bface @@ Desc.Constr.boundary constr in
          let vty = Ty.eval cx clause_ty in
          Q.equate_con_sys (Cx.qenv cx) (Cx.rel cx) vty val_sys val_sys
        in


        (* We run the clause tactic with the goal type restricted by the boundary above *)
        kont_tac clause_tac {ty = clause_ty; sys = tsys} <<@> fun bdy ->
          clbl, Tm.bindn (Bwd.map fst @@ Bwd.from_list psi) bdy
      end
    in

    M.Util.fold_left (fun acc clause -> refine_clause acc clause <<@> fun cl -> cl :: acc) [] eclauses >>= fun clauses ->
    M.ret @@ Tm.up @@ Tm.ann ~ty:data_ty ~tm:scrut @< Tm.Elim {dlbl; params; mot = bmot; clauses}

let rec tac_hope goal =
  let rec try_system sys =
    match sys with
    | [] ->
      C.ask >>= fun psi ->
      let rty = Tm.refine_ty goal.ty goal.sys in
      U.push_hole `Flex psi rty <<@> fun cmd -> Tm.up @@ Tm.refine_force cmd
    | (r, r', tm) :: sys ->
      begin
        C.check ~ty:goal.ty ~sys:goal.sys tm >>=
        function
        | `Ok ->
          M.ret tm
        | _ ->
          try_system sys
      end
  in
  try_system goal.sys

let tac_guess tac : chk_tac =
  fun goal ->
    tac {goal with sys = []} >>= fun tm ->
    let rty = Tm.refine_ty goal.ty goal.sys in
    let rty0 = Tm.refine_ty goal.ty [] in
    C.ask >>= fun psi ->
    U.push_guess psi ~ty0:rty ~ty1:rty0 (Tm.refine_thunk tm) <<@> fun tm ->
      Tm.up @@ Tm.refine_force @@ Tm.ann ~ty:rty ~tm

let tac_refl =
  tac_fix @@ fun tac_refl ->
  normalizing_goal @@ match_goal @@ fun goal ->
  match Tm.unleash goal.ty with
  | Tm.Ext (Tm.NB (nms, _)) ->
    let xs = Bwd.to_list @@ Bwd.map (fun x -> `Var (`Gen (Name.named x))) nms in
    tac_lambda xs tac_refl

  | Tm.Pi (dom, Tm.B (nm, _)) ->
    let xs = [`Var (`Gen (Name.named nm))] in
    tac_lambda xs tac_refl

  | Tm.Sg (_, _) ->
    tac_pair tac_refl tac_refl

  | _ ->
    tac_hope

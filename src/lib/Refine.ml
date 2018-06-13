(* Experimental code *)

open RedBasis
open Bwd open BwdNotation open Dev

module type Import =
sig
  val import : Lwt_io.file_name -> ESig.esig
end

module Make (I : Import) =
struct

  module C = Contextual
  module U = Unify

  module M :
  sig
    include Monad.S

    val lift : 'a C.m -> 'a m
    val in_scope : Name.t -> ty param -> 'a m -> 'a m
    val in_scopes : (Name.t * ty param) list -> 'a m -> 'a m
    val under_restriction : tm -> tm -> 'a m -> 'a m

    val isolate : 'a m -> 'a m

    type diagnostic =
      | UserHole of {name : string option; tele : U.telescope; ty : Tm.tm; tm : Tm.tm}

    val emit : diagnostic -> unit m
    val report : 'a m -> 'a m

    val run : 'a m -> 'a
  end =
  struct
    type diagnostic =
      | UserHole of {name : string option; tele : U.telescope; ty : Tm.tm; tm : Tm.tm}

    type 'a m = ('a * diagnostic bwd) C.m


    let ret a =
      C.ret (a, Emp)

    let bind m k =
      C.bind m @@ fun (a, w) ->
      C.bind (k a) @@ fun (b, w') ->
      C.ret (b, w <.> w')

    let lift m =
      C.bind m ret

    let emit d =
      C.ret ((), Emp #< d)

    let print_diagnostic =
      function
      | UserHole {name; tele; ty; tm} ->
        C.local (fun _ -> tele) @@
        begin
          C.bind C.typechecker @@ fun (module T) ->
          Format.printf "?%s:@,  @[<v>@[<v>%a@]@,%a %a@,%a %a@]@.@."
            (match name with Some name -> name | None -> "Hole")
            Dev.pp_params tele
            Uuseg_string.pp_utf_8 "⊢"
            Tm.pp0 ty
            Uuseg_string.pp_utf_8 "⟿"
            Tm.pp0 tm;
          C.ret ()
        end

    let rec print_diagnostics =
      function
      | Emp ->
        C.ret ()
      | Snoc (w, d) ->
        C.bind (print_diagnostics w) @@ fun _ ->
        print_diagnostic d

    let report (m : 'a m) : 'a m =
      C.bind m @@ fun (a, w) ->
      C.bind (C.dump_state Format.err_formatter "Unsolved:" `Unsolved) @@ fun _ ->
      C.bind (print_diagnostics w) @@ fun _ ->
      ret a


    let under_restriction = C.under_restriction
    let in_scopes = C.in_scopes
    let in_scope = C.in_scope
    let isolate = C.isolate


    let run m =
      fst @@ C.run m
  end



  open Dev open Unify
  module Notation = Monad.Notation (M)
  open Notation

  module E = ESig
  module T = Map.Make (String)

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
        begin
          match Name.name x with
          | Some str ->
            let renvx = ResEnv.global str x renv in
            go_locals renvx psi
          | None ->
            go_locals renv psi
        end
    in
    M.lift C.ask >>= fun psi ->
    let renv = go_globals (ResEnv.init ()) @@ T.bindings env in
    M.ret @@ go_locals renv psi


  let normalize_ty ty =
    M.lift C.typechecker >>= fun (module T) ->
    let vty = T.Cx.eval T.Cx.emp ty in
    M.ret @@ T.Cx.quote_ty T.Cx.emp vty

  let (<+>) m n =
    C.bind (C.optional m) @@
    function
    | Some x -> C.ret x
    | None -> n

  let rec elab_sig env =
    function
    | [] ->
      M.ret env
    | E.Debug f :: esig ->
      elab_decl env (E.Debug f) >>= fun env' ->
      elab_sig env' esig
    | dcl :: esig ->
      M.isolate
        begin
          elab_decl env dcl >>= fun env' ->
          M.lift C.go_to_top >> (* This is suspicious, in connection with the other suspicious thing *)
          M.lift U.ambulando >>
          M.ret env'
        end >>= fun env' ->
      elab_sig env' esig


  and elab_decl env =
    function
    | E.Define (name, scheme, e) ->
      elab_scheme env scheme @@ fun cod ->
      elab_chk env cod e >>= fun tm ->
      let alpha = Name.named @@ Some name in

      M.lift C.ask >>= fun psi ->
      M.lift @@ U.define psi alpha cod tm >>= fun _ ->
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
      let esig = I.import file_name in
      elab_sig env esig

  and elab_scheme env (cells, ecod) kont =
    let rec go gm =
      function
      | [] ->
        elab_chk env univ ecod >>=
        normalize_ty >>=
        kont
      | (name, edom) :: cells ->
        elab_chk env univ edom >>= normalize_ty >>= fun dom ->
        let x = Name.named @@ Some name in
        M.in_scope x (`P dom) @@
        go (gm #< (x, dom)) cells
    in
    go Emp cells

  and guess_restricted ty sys tm =
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
    let rty = Tm.make @@ Tm.Rst {ty; sys} in
    M.lift C.ask >>= fun psi ->
    M.lift @@ U.push_guess psi ~ty0:rty ~ty1:ty tm

  and elab_chk env ty e : tm M.m =
    match Tm.unleash ty, e with

    | _, E.Let info ->
      begin
        match info.ty with
        | None ->
          elab_inf env info.tm >>= fun (let_ty, let_tm) ->
          M.ret (let_ty, Tm.up let_tm)
        | Some ety ->
          elab_chk env univ ety >>= fun let_ty ->
          elab_chk env let_ty info.tm >>= fun let_tm ->
          M.ret (let_ty, let_tm)
      end >>= fun (let_ty, let_tm) ->
      let singleton_ty =
        let face = Tm.make Tm.Dim0, Tm.make Tm.Dim0, Some let_tm in
        Tm.make @@ Tm.Rst {ty = let_ty; sys = [face]}
      in
      let x = Name.named @@ Some info.name in
      M.in_scope x (`P singleton_ty)
        begin
          elab_chk env ty info.body
        end >>= fun bdyx ->
      let inf = Tm.Down {ty = let_ty; tm = let_tm}, Emp in
      M.ret @@ Tm.make @@ Tm.Let (inf, Tm.bind x bdyx)

    | Tm.Rst info, _ ->
      elab_chk env info.ty e >>=
      guess_restricted info.ty info.sys

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


    | _, E.Lam ([], e) ->
      elab_chk env ty e

    | Tm.Univ _, E.Pi ([], e) ->
      elab_chk env ty e

    | Tm.Univ _, E.Pi ((name, edom) :: etele, ecod) ->
      elab_chk env ty edom >>= fun dom ->
      let x = Name.named @@ Some name in
      M.in_scope x (`P dom) begin
        elab_chk env ty @@ E.Pi (etele, ecod)
      end >>= fun codx ->
      M.ret @@ Tm.make @@ Tm.Pi (dom, Tm.bind x codx)

    | Tm.Pi (dom, cod), E.Lam (name :: names, e) ->
      let x = Name.named @@ Some name in
      let codx = Tm.unbind_with x (fun _ -> `Only) cod in
      M.in_scope x (`P dom) begin
        elab_chk env codx @@
        E.Lam (names, e)
      end >>= fun bdyx ->
      M.ret @@ Tm.make @@ Tm.Lam (Tm.bind x bdyx)


    | Tm.Ext ((Tm.NB (nms, _)) as ebnd), E.Lam (names, e) ->
      let rec bite nms lnames rnames =
        match nms, rnames with
        | [], _ -> lnames, E.Lam (rnames, e)
        | _ :: nms, name :: rnames ->
          let x = Name.named @@ Some name in
          bite nms (lnames #< x) rnames
        | _ -> failwith "Elab: incorrect number of binders when refining extension type"
      in
      let xs, e' = bite nms Emp names in
      let fwd_xs = Bwd.to_list xs in
      let ty, sys = Tm.unbind_ext_with fwd_xs ebnd in
      let rty = Tm.make @@ Tm.Rst {ty; sys} in
      let ps = List.map (fun x -> (x, `I)) fwd_xs in
      M.in_scopes ps begin
        elab_chk env rty e'
      end >>= fun bdyxs ->
      M.ret @@ Tm.make @@ Tm.ExtLam (Tm.bindn xs bdyxs)


    | _, Tuple [] ->
      failwith "empty tuple"
    | _, Tuple [e] ->
      elab_chk env ty e
    | Tm.Sg (dom, cod), Tuple (e :: es) ->
      elab_chk env dom e >>= fun tm0 ->
      M.lift C.typechecker >>= fun (module T) ->
      let module HS = HSubst (T) in
      let vdom = T.Cx.eval T.Cx.emp dom in
      let cod' = HS.inst_ty_bnd cod (vdom, tm0) in
      elab_chk env cod' (Tuple es) >>= fun tm1 ->
      M.ret @@ Tm.cons tm0 tm1

    | _, Type ->
      begin
        match Tm.unleash ty with
        | Tm.Univ _ ->
          M.ret @@ Tm.univ ~kind:Kind.Kan ~lvl:(Lvl.Const 0)
        | _ ->
          failwith "Type"
      end

    | _, E.Hole name ->
      M.lift C.ask >>= fun psi ->
      M.lift @@ U.push_hole `Rigid psi ty >>= fun tm ->
      M.emit @@ M.UserHole {name; ty; tele = psi; tm = Tm.up tm} >>
      M.ret @@ Tm.up tm

    | _, E.Hope ->
      M.lift C.ask >>= fun psi ->
      M.lift @@ U.push_hole `Flex psi ty >>= fun tm ->
      M.ret @@ Tm.up tm

    | _, E.Cut (e, fs) ->
      elab_inf env e >>= fun (hty, hd) ->
      elab_chk_cut env (hty, hd) fs ty

    | _, e ->
      elab_up env ty e

  and elab_up env ty inf =
    elab_inf env inf >>= fun (ty', cmd) ->
    M.lift (C.check_subtype ty' ty) >>= fun b ->
    if b then M.ret @@ Tm.up cmd else
      begin
        M.lift @@ C.active @@ Dev.Subtype {ty0 = ty'; ty1 = ty} >>
        M.lift C.ask >>= fun psi ->
        M.lift @@ U.push_guess psi ~ty0:ty ~ty1:ty' (Tm.up cmd)
      end

  and elab_inf env e : (ty * tm Tm.cmd) M.m =
    match e with
    | E.Var name ->
      get_resolver env >>= fun renv ->
      begin
        match ResEnv.get name renv with
        | `Ref a ->
          M.lift (C.lookup_var a `Only <+> C.bind (C.lookup_meta a) (fun (ty, _) -> C.ret ty)) >>= fun ty ->
          let cmd = Tm.Ref (a, `Only), Emp in
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
          M.lift C.typechecker >>= fun (module T) ->
          let vty = T.infer T.Cx.emp cmd in
          M.ret (T.Cx.quote_ty T.Cx.emp vty, cmd)
        | _ ->
          failwith "Cannot elaborate `term"
      end

    | E.Cut (e, fs) ->
      elab_inf_cut env e (Bwd.from_list fs)


    | _ ->
      failwith "Can't infer"

  and elab_dim env e =
    match e with
    | E.Var name ->
      get_resolver env >>= fun renv ->
      begin
        match ResEnv.get name renv with
        | `Ref a ->
          M.ret @@ Tm.up (Tm.Ref (a, `Only), Emp)
        | `Ix _ ->
          failwith "elab_inf: expected locally closed"
      end
    | _ ->
      failwith "TODO: elab_dim"

  and elab_chk_cut env (hty, cmd) efs ty =
    let rec go hty (hd, sp) efs =
      match Tm.unleash hty, efs with
      | _, [] ->
        let tm = Tm.up (hd, sp) in
        M.lift (C.check_subtype hty ty) >>= fun b ->
        if b then M.ret tm else
          begin
            M.lift @@ C.active @@ Dev.Subtype {ty0 = hty; ty1 = ty} >>
            M.lift C.ask >>= fun psi ->
            M.lift @@ U.push_guess psi ~ty0:ty ~ty1:hty tm
          end

      | Tm.Pi (dom, cod), E.App e :: efs ->
        elab_chk env dom e >>= fun t ->
        M.lift C.typechecker >>= fun (module T) ->
        let module HS = HSubst (T) in
        let vdom = T.Cx.eval T.Cx.emp dom in
        let cod' = HS.inst_ty_bnd cod (vdom, t) in
        go cod' (hd, sp #< (Tm.FunApp t)) efs

      | Tm.Ext ebnd, efs ->
        let xs, ext_ty, _ = Tm.unbind_ext ebnd in
        let rec bite rs xs efs =
          match xs, efs with
          | Emp, _ ->
            M.ret (Bwd.to_list rs, efs)
          | Snoc (xs, _), E.App e :: efs ->
            elab_dim env e >>= fun r ->
            bite (rs #< r) xs efs
          | _ ->
            failwith "elab_chk_cut: problem biting extension type"
        in
        bite Emp xs efs >>= fun (rs, efs) ->
        go ext_ty (hd, sp #< (Tm.ExtApp rs)) efs

      | Tm.Sg (dom, _), E.Car :: efs ->
        go dom (hd, sp) efs

      | Tm.Sg (_, Tm.B (_, cod)), E.Cdr :: efs ->
        let cod' = Tm.subst (Tm.Sub (Tm.Id, (hd, sp #< Tm.Car))) cod in
        go cod' (hd, sp #< Tm.Cdr) efs

      | Tm.Rst rst, efs ->
        go rst.ty (hd, sp) efs

      | _ -> failwith "elab_chk_cut: unexpected case"
    in
    go hty cmd efs

  and elab_inf_cut env e efs =
    match efs with
    | Emp ->
      elab_inf env e
    | Snoc (efs, frm) ->
      elab_inf_cut env e efs >>= fun (ty, (hd, sp)) ->
      elab_inf_frame env (ty, (hd, sp)) frm

  and elab_inf_frame env (ty, (hd, sp)) efs =
    match Tm.unleash ty, efs with
    | Tm.Rst rst, _ ->
      elab_inf_frame env (rst.ty, (hd, sp)) efs

    | Tm.Pi (dom, cod), E.App e ->
      elab_chk env dom e >>= fun t ->
      M.lift C.typechecker >>= fun (module T) ->
      let module HS = HSubst (T) in
      let vdom = T.Cx.eval T.Cx.emp dom in
      let cod' = HS.inst_ty_bnd cod (vdom, t) in
      M.ret (cod', (hd, sp #< (Tm.FunApp t)))

    | Tm.Sg (dom, _), E.Car ->
      M.ret (dom, (hd, sp #< Tm.Car))

    | Tm.Sg (_, Tm.B (_, cod)), E.Cdr ->
      let cod' = Tm.subst (Tm.Sub (Tm.Id, (hd, sp #< Tm.Car))) cod in
      M.ret (cod', (hd, sp #< Tm.Cdr))

    (* | Tm.Ext ebnd, efs ->
       let xs, ext_ty, _ = Tm.unbind_ext ebnd in
       let rec bite rs xs efs =
        match xs, efs with
        | Emp, _ ->
          M.ret (Bwd.to_list rs, efs)
        | Snoc (xs, _), E.App e :: efs ->
          elab_dim env e >>= fun r ->
          bite (rs #< r) xs efs
        | _ ->
          failwith "elab_chk_cut: problem biting extension type"
       in
       bite Emp xs efs >>= fun (rs, efs) ->
       M.ret (ext_ty, (hd, sp #< (Tm.ExtApp rs))) *)

    | _ -> failwith "TODO: elab_inf_frame"

end


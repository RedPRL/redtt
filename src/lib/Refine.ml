(* Experimental code *)

open RedBasis
open Bwd open BwdNotation open Dev

module type Import =
sig
  val import : Lwt_io.file_name -> [`Elab of ESig.esig | `Cached]
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
    val under_restriction : tm -> tm -> 'a m -> 'a option m
    val local : (params -> params) -> 'a m -> 'a m

    val isolate : 'a m -> 'a m
    val unify : unit m

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
          let vty = T.Cx.eval T.Cx.emp ty in
          let ty = T.Cx.quote_ty T.Cx.emp vty in
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


    let under_restriction r r' (m : 'a m) : 'a option m =
      C.bind (C.under_restriction r r' m) @@ function
      | None ->
        ret None
      | Some (x, ds) ->
        C.ret (Some x, ds)

    let in_scopes = C.in_scopes
    let in_scope = C.in_scope
    let isolate = C.isolate
    let unify = lift @@ C.bind C.go_to_top @@ fun _ -> C.local (fun _ -> Emp) U.ambulando
    let local = C.local


    let run m =
      fst @@ C.run m
  end



  open Dev open Unify
  module Notation = Monad.Notation (M)
  open Notation

  module E = ESig
  module T = Map.Make (String)

  type _ mode =
    | Chk : ty -> tm mode
    | Inf : (ty * tm Tm.cmd) mode

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
      M.isolate (elab_decl env dcl) >>= fun env' ->
      elab_sig env' esig


  and elab_decl env =
    function
    | E.Define (name, scheme, e) ->
      elab_scheme env scheme @@ fun cod ->
      M.unify >>
      elab_chk env cod e >>= fun tm ->
      let alpha = Name.named @@ Some name in

      M.lift C.ask >>= fun psi ->
      M.lift @@ U.define psi alpha cod tm >>= fun _ ->
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
    let rty = Tm.make @@ Tm.Rst {ty; sys} in
    M.lift @@ C.check ~ty:rty tm >>= fun b ->
    if b then M.ret tm else
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
      M.lift C.ask >>= fun psi ->
      M.lift @@ U.push_guess psi ~ty0:rty ~ty1:ty tm

  and elab_chk env ty e : tm M.m =
    normalize_ty ty >>= fun ty ->
    match Tm.unleash ty, e with
    | _, E.Hole name ->
      M.lift C.ask >>= fun psi ->
      M.lift @@ U.push_hole `Rigid psi ty >>= fun tm ->
      M.emit @@ M.UserHole {name; ty; tele = psi; tm = Tm.up tm} >>
      M.ret @@ Tm.up tm

    | _, E.Hope ->
      M.lift C.ask >>= fun psi ->
      M.lift @@ U.push_hole `Flex psi ty >>= fun tm ->
      M.ret @@ Tm.up tm


    | _, E.Let info ->
      begin
        match info.ty with
        | None ->
          elab_inf env info.tm >>= fun (let_ty, let_tm) ->
          M.ret (let_ty, Tm.up let_tm)
        | Some ety ->
          elab_chk env univ ety >>= fun let_ty ->
          normalize_ty let_ty >>= fun let_ty ->
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

    | _, E.If (escrut, etcase, efcase) ->
      let univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kind.Pre in
      let bool = Tm.make @@ Tm.Bool in
      elab_chk env bool escrut >>= fun scrut ->

      let is_dependent =
        match Tm.unleash scrut with
        | Tm.Up (Tm.Ref (a, _), _) when Occurs.Set.mem a @@ Tm.free `Vars ty -> true
        | _ -> false
      in

      begin
        if is_dependent then
          M.lift @@ push_hole `Flex Emp (Tm.pi None bool univ) >>= fun (mothd, motsp) ->
          let mot arg = Tm.up (mothd, motsp #< (Tm.FunApp arg)) in
          M.lift @@ C.active @@ Problem.eqn ~ty0:univ ~ty1:univ ~tm0:ty ~tm1:(mot scrut) >>
          M.unify >>

          normalize_ty (mot @@ Tm.make Tm.Tt) >>= fun mot_tt ->
          normalize_ty (mot @@ Tm.make Tm.Ff) >>= fun mot_ff ->
          M.ret (mot, mot_tt, mot_ff)
        else
          M.ret ((fun _ -> ty), ty, ty)
      end >>= fun (mot, mot_tt, mot_ff) ->

      elab_chk env mot_tt etcase >>= fun tcase ->
      elab_chk env mot_ff efcase >>= fun fcase ->
      let hd = Tm.Down {ty = bool; tm = scrut} in
      let bmot =
        let x = Name.fresh () in
        Tm.bind x @@ mot @@ Tm.up (Tm.Ref (x, `Only), Emp)
      in
      let frm = Tm.If {mot = bmot; tcase; fcase} in
      M.ret @@ Tm.up (hd, Emp #< frm)

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
      M.ret @@ Tm.make @@ Tm.Ext ebnd

    | Tm.Univ _, E.Rst (ety, esys) ->
      let univ = ty in
      elab_chk env univ ety >>= fun ty ->
      elab_tm_sys env ty esys >>= fun sys ->
      M.ret @@ Tm.make @@ Tm.Rst {ty; sys}

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

    | Tm.Univ _, E.Sg ([], e) ->
      elab_chk env ty e

    | Tm.Univ _, E.Sg ((name, edom) :: etele, ecod) ->
      elab_chk env ty edom >>= fun dom ->
      let x = Name.named @@ Some name in
      M.in_scope x (`P dom) begin
        elab_chk env ty @@ E.Sg (etele, ecod)
      end >>= fun codx ->
      M.ret @@ Tm.make @@ Tm.Sg (dom, Tm.bind x codx)

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
      let ty, sys = Tm.unbind_ext_with (Bwd.to_list xs) ebnd in
      let rty = Tm.make @@ Tm.Rst {ty; sys} in
      let ps = List.map (fun x -> (x, `I)) @@ Bwd.to_list xs in
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

    | _, E.Cut (e, fs) ->
      elab_inf env e >>= fun (hty, hd) ->
      normalize_ty hty >>= fun hty ->
      elab_cut env (hty, hd) fs (Chk ty)

    | _, E.HCom info ->
      elab_dim env info.r >>= fun r ->
      elab_dim env info.r' >>= fun r' ->
      let kan_univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kan in
      begin
        M.lift @@ C.check ~ty:kan_univ ty >>= function
        | true ->
          elab_chk env ty info.cap >>= fun cap ->
          elab_hcom_sys env r ty cap info.sys >>= fun sys ->
          let hcom = Tm.HCom {r; r'; ty; cap; sys} in
          M.ret @@ Tm.up (hcom, Emp)

        | false ->
          failwith "Cannot compose in a type that isn't Kan"
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
        let varx = Tm.up (Tm.Ref (x, `Only), Emp) in
        let ext_ty =
          let face_cap = varx, s, Some cap in
          let face_adj (r, r', obnd) =
            let bnd = Option.get_exn obnd in
            let tmx = Tm.unbind_with x (fun tw -> tw) bnd in
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
            M.lift C.typechecker >>= fun (module T) ->
            let module HS = HSubst (T) in
            let _, tmx = HS.((ext_ty, line) %% Tm.ExtApp [varx]) in
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
        let varx = Tm.up (Tm.Ref (x, `Only), Emp) in
        let tyx = Tm.unbind_with x (fun tw -> tw) ty_bnd in
        let ext_ty =
          let face_cap = varx, s, Some cap in
          let face_adj (r, r', obnd) =
            let bnd = Option.get_exn obnd in
            let tmx = Tm.unbind_with x (fun tw -> tw) bnd in
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
            M.lift C.typechecker >>= fun (module T) ->
            let module HS = HSubst (T) in
            let _, tmx = HS.((ext_ty, line) %% Tm.ExtApp [varx]) in
            M.ret @@ Tm.bind x tmx
          end
        end >>= fun obnd ->
        let face = r, r', obnd in
        go (acc #< face) esys

    in go Emp

  and elab_up env ty inf =
    elab_inf env inf >>= fun (ty', cmd) ->
    M.lift (C.check_subtype ty' ty) >>= fun b ->
    if b then M.ret @@ Tm.up cmd else
      (* TODO: I really don't like this; it leads to confusing, RedPRL-style proof states where you don't know if you're wrong.
         We should be more conservative, and try to immediately solve the problem with unification, and if that fails, throw an error. *)
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
      elab_inf env e >>= fun (ty, cmd) ->
      normalize_ty ty >>= fun ty ->
      elab_cut env (ty, cmd) fs Inf

    | E.Coe info ->
      elab_dim env info.r >>= fun tr ->
      elab_dim env info.r' >>= fun tr' ->
      let x = Name.fresh () in
      let kan_univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kind.Kan in
      let univ_fam = Tm.make @@ Tm.Ext (Tm.bind_ext (Emp #< x) kan_univ []) in
      elab_chk env univ_fam info.fam >>= fun fam ->
      M.lift C.typechecker >>= fun (module T) ->
      let module HS = HSubst (T) in
      let _, fam_r = HS.((univ_fam, fam) %% Tm.ExtApp [tr]) in
      elab_chk env fam_r info.tm >>= fun tm ->
      let _, fam_r' = HS.((univ_fam, fam) %% Tm.ExtApp [tr']) in
      let varx = Tm.up (Tm.Ref (x, `Only), Emp) in
      let _, tyx = HS.((univ_fam, fam) %% Tm.ExtApp [varx]) in
      let coe = Tm.Coe {r = tr; r' = tr'; ty = Tm.bind x tyx; tm} in
      M.ret (fam_r', (coe, Emp))

    | E.Com info ->
      elab_dim env info.r >>= fun tr ->
      elab_dim env info.r' >>= fun tr' ->
      let x = Name.fresh () in
      let kan_univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kind.Kan in
      let univ_fam = Tm.make @@ Tm.Ext (Tm.bind_ext (Emp #< x) kan_univ []) in
      elab_chk env univ_fam info.fam >>= fun fam ->
      M.lift C.typechecker >>= fun (module T) ->
      let module HS = HSubst (T) in
      let _, fam_r = HS.((univ_fam, fam) %% Tm.ExtApp [tr]) in
      elab_chk env fam_r info.cap >>= fun cap ->
      let _, fam_r' = HS.((univ_fam, fam) %% Tm.ExtApp [tr']) in
      let varx = Tm.up (Tm.Ref (x, `Only), Emp) in
      let _, tyx = HS.((univ_fam, fam) %% Tm.ExtApp [varx]) in
      let tybnd = Tm.bind x tyx in
      elab_com_sys env tr tybnd cap info.sys >>= fun sys ->
      let com = Tm.Com {r = tr; r' = tr'; ty = tybnd; cap; sys} in
      M.ret (fam_r', (com, Emp))

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
          failwith "elab_dim: expected locally closed"
      end
    | E.Num 0 ->
      M.ret @@ Tm.make Tm.Dim0
    | E.Num 1 ->
      M.ret @@ Tm.make Tm.Dim1
    | _ ->
      failwith "TODO: elab_dim"

  and elab_cut : type x. _ -> (ty * tm Tm.cmd) -> E.frame list -> x mode -> x M.m =
    fun (type x) env ->
      let rec go : ty -> _ -> _ -> x mode -> x M.m =
        fun (hty : ty) (hd, sp) efs mode : x M.m ->
          match Tm.unleash hty, efs with
          | _, [] ->
            begin
              match mode with
              | Chk ty ->
                M.lift (C.check_subtype hty ty) >>= fun b ->
                if b then M.ret (Tm.up (hd, sp)) else
                  let tm = Tm.up (hd, sp) in
                  M.lift @@ C.active @@ Dev.Subtype {ty0 = hty; ty1 = ty} >>
                  M.lift C.ask >>= fun psi ->
                  M.lift @@ U.push_guess psi ~ty0:ty ~ty1:hty tm >>= fun tm ->
                  M.ret tm

              | Inf ->
                M.ret (hty, (hd, sp))
            end

          | Tm.Pi (dom, cod), E.App e :: efs ->
            elab_chk env dom e >>= fun t ->
            M.lift C.typechecker >>= fun (module T) ->
            let module HS = HSubst (T) in
            let vdom = T.Cx.eval T.Cx.emp dom in
            let cod' = HS.inst_ty_bnd cod (vdom, t) in
            go cod' (hd, sp #< (Tm.FunApp t)) efs mode

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
                failwith "elab_cut: problem biting extension type"
            in
            bite Emp xs efs >>= fun (rs, efs) ->
            go ext_ty (hd, sp #< (Tm.ExtApp rs)) efs mode

          | Tm.Sg (dom, _), E.Car :: efs ->
            go dom (hd, sp #< Tm.Car) efs mode

          | Tm.Sg (_, Tm.B (_, cod)), E.Cdr :: efs ->
            let cod' = Tm.subst (Tm.Sub (Tm.Id, (hd, sp #< Tm.Car))) cod in
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


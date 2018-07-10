open RedBasis
open RedTT_Core
open Dev open Bwd open BwdNotation

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
  M.lift C.typechecker >>= fun (module T) ->
  let vty = T.Cx.eval T.Cx.emp ty in
  let ty = T.Cx.quote_ty T.Cx.emp vty in
  let now1 = Unix.gettimeofday () in
  normalization_clock := !normalization_clock +. (now1 -. now0);
  M.ret ty


let guess_restricted ty sys tm =
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
    M.unify >>
    M.lift @@ C.check ~ty:rty tm >>= fun b ->
    if b then M.ret tm else
      begin
        M.lift @@ C.dump_state Format.err_formatter "damn" `All >>= fun _ ->
        failwith "guess_restricted: type error"
      end

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
      let vars = Bwd.to_list @@ Bwd.map (fun x -> Tm.up @@ Tm.var x) xs in
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

let tac_if ~tac_mot ~tac_scrut ~tac_tcase ~tac_fcase =
  fun ty ->
    let univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kind.Pre in
    let bool = Tm.make @@ Tm.Bool in
    tac_scrut bool >>= fun scrut ->
    begin
      match tac_mot with
      | None ->
        let is_dependent =
          match Tm.unleash scrut with
          | Tm.Up (Tm.Var {name; _}, _) when Occurs.Set.mem name @@ Tm.free `Vars ty -> true
          | _ -> false
        in
        if is_dependent then
          let mot_ty = Tm.pi None bool univ in
          M.lift @@ U.push_hole `Flex Emp mot_ty >>= fun (mothd, motsp) ->
          let mot arg = Tm.up (mothd, motsp #< (Tm.FunApp arg)) in
          M.lift @@ C.active @@ Problem.eqn ~ty0:univ ~ty1:univ ~tm0:ty ~tm1:(mot scrut) >>
          M.unify >>
          let mot_tt = mot @@ Tm.make Tm.Tt in
          let mot_ff = mot @@ Tm.make Tm.Ff in
          M.ret (mot, mot_tt, mot_ff)
        else
          M.ret ((fun _ -> ty), ty, ty)
      | Some tac_mot ->
        let mot_ty = Tm.pi None bool univ in
        tac_mot mot_ty >>= fun mot ->
        let fmot arg = Tm.up (Tm.Down {ty = mot_ty; tm = mot}, Emp #< (Tm.FunApp arg)) in
        let mot_tt = fmot @@ Tm.make Tm.Tt in
        let mot_ff = fmot @@ Tm.make Tm.Ff in
        M.ret (fmot, mot_tt, mot_ff)
    end >>= fun (mot, mot_tt, mot_ff) ->
    tac_tcase mot_tt >>= fun tcase ->
    tac_fcase mot_ff >>= fun fcase ->
    let hd = Tm.Down {ty = bool; tm = scrut} in
    let bmot =
      let x = Name.fresh () in
      Tm.bind x @@ mot @@ Tm.up @@ Tm.var x
    in
    let frm = Tm.If {mot = bmot; tcase; fcase} in
    M.ret @@ Tm.up (hd, Emp #< frm)


let rec tac_lambda names tac ty =
  match Tm.unleash ty with
  | Tm.Pi (dom, cod) ->
    begin
      match names with
      | [] -> tac ty
      | name :: names ->
        let x = Name.named @@ Some name in
        let codx = Tm.unbind_with x cod in
        M.in_scope x (`P dom) begin
          tac_wrap_nf (tac_lambda names tac) codx
        end >>= fun bdyx ->
        M.ret @@ Tm.make @@ Tm.Lam (Tm.bind x bdyx)
    end

  | Tm.Ext (Tm.NB (nms, _) as ebnd) ->
    begin
      match names with
      | [] -> tac ty
      | _ ->
        let rec bite nms lnames rnames =
          match nms, rnames with
          | [], _ -> lnames, tac_wrap_nf (tac_lambda rnames tac)
          | _ :: nms, name :: rnames ->
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
        M.ret @@ Tm.make @@ Tm.ExtLam (Tm.bindn xs bdyxs)
    end

  | _ ->
    begin
      match names with
      | [] -> tac ty
      | _ ->
        raise ChkMatch
    end

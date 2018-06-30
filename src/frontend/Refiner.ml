open RedBasis
open RedTT_Core
open Dev open Bwd open BwdNotation

module M = ElabMonad
module C = Contextual
module U = Unify
module Notation = Monad.Notation (M)
open Notation

type chk_tac = ty -> tm M.m

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
    M.lift C.ask >>= fun psi ->
    M.lift @@ U.push_guess psi ~ty0:rty ~ty1:ty tm

exception ChkMatch

(* The idea of this function is to push a restriction downward into a negative type.
   It is perhaps a bit too ambitious to fully unleash, until we have developed the
   subtyping and definitional equivalence theory that really gets down with eta laws. *)
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
      let var = Tm.up (Tm.Ref {name = x; ushift = 0; twin = `Only}, Emp) in
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
      let vars = Bwd.to_list @@ Bwd.map (fun x -> Tm.up (Tm.Ref {name = x; ushift = 0; twin = `Only}, Emp)) xs in
      let hd = Tm.Down {ty; tm} in
      Tm.up (hd , Emp #< (Tm.ExtApp vars))
    in
    let ebnd' = Tm.bind_ext xs tyxs @@ sysxs @ on_sys app_tm sys in
    let rty = Tm.make @@ Tm.Ext ebnd' in
    M.ret @@ `Negative rty


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

let rec tac_lambda names tac ty =
  match Tm.unleash ty with
  | Tm.Pi (dom, cod) ->
    begin
      match names with
      | [] -> tac ty
      | name :: names ->
        let x = Name.named @@ Some name in
        let codx = Tm.unbind_with x (fun _ -> `Only) cod in
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

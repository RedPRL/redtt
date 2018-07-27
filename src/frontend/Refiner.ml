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

let tac_if ~tac_mot ~tac_scrut ~tac_tcase ~tac_fcase =
  fun ty ->
    let univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kind.Pre in
    let bool = Tm.make @@ Tm.Bool in
    let mot_ty = Tm.pi None bool univ in
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
    let mot_tt = mot @@ Tm.make Tm.Tt in
    let mot_ff = mot @@ Tm.make Tm.Ff in
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

let tac_nat_rec ~tac_mot ~tac_scrut ~tac_zcase ~tac_scase:(nm_scase, nm_rec_scase, tac_scase) =
  fun ty ->
    let univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kind.Pre in
    let nat = Tm.make @@ Tm.Nat in
    let mot_ty = Tm.pi None nat univ in
    let x_scase = Name.named @@ Some nm_scase in
    let x_rec_scase = Name.named nm_rec_scase in
    tac_scrut nat >>= fun scrut ->
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
    tac_zcase (mot (Tm.make Tm.Zero)) >>= fun zcase ->
    let mot_suc_x = mot (Tm.make (Tm.Suc (Tm.up (Tm.var x_scase)))) in
    M.in_scopes [x_scase, `P nat; x_rec_scase, `P (mot @@ Tm.up @@ Tm.var x_scase)] begin
      tac_scase mot_suc_x >>= fun tm ->
      M.ret @@ Tm.bindn (Emp #< x_scase #< x_rec_scase) tm
    end >>= fun scase ->
    let hd = Tm.Down {ty = nat; tm = scrut} in
    let bmot =
      let x = Name.fresh () in
      Tm.bind x @@ mot @@ Tm.up @@ Tm.var x
    in
    let frm = Tm.NatRec {mot = bmot; zcase; scase} in
    M.ret @@ Tm.up (hd, Emp #< frm)

let tac_int_rec ~tac_mot ~tac_scrut ~tac_pcase:(nm_pcase, tac_pcase) ~tac_ncase:(nm_ncase, tac_ncase) =
  fun ty ->
    let univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kind.Pre in
    let nat = Tm.make @@ Tm.Nat in
    let int = Tm.make @@ Tm.Int in
    let mot_ty = Tm.pi None int univ in
    let x_pcase = Name.named @@ Some nm_pcase in
    let x_ncase = Name.named @@ Some nm_ncase in
    tac_scrut int >>= fun scrut ->
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
    let mot_pos_x = mot (Tm.make (Tm.Pos (Tm.up (Tm.var x_pcase)))) in
    M.in_scope x_pcase (`P nat) begin
      tac_pcase mot_pos_x >>= fun tm ->
      M.ret @@ Tm.bind x_pcase tm
    end >>= fun pcase ->
    let mot_negsuc_x = mot (Tm.make (Tm.NegSuc (Tm.up (Tm.var x_ncase)))) in
    M.in_scope x_ncase (`P nat) begin
      tac_ncase mot_negsuc_x >>= fun tm ->
      M.ret @@ Tm.bind x_ncase tm
    end >>= fun ncase ->
    let hd = Tm.Down {ty = int; tm = scrut} in
    let bmot =
      let x = Name.fresh () in
      Tm.bind x @@ mot @@ Tm.up @@ Tm.var x
    in
    let frm = Tm.IntRec {mot = bmot; pcase; ncase} in
    M.ret @@ Tm.up (hd, Emp #< frm)

let tac_s1_rec ~tac_mot ~tac_scrut ~tac_bcase ~tac_lcase:(nm_lcase, tac_lcase) =
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

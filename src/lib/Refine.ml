(* Experimental code *)

open RedBasis
open Bwd open BwdNotation open Dev

module C = Contextual
module U = Unify

module M :
sig
  include Monad.S

  val lift : 'a C.m -> 'a m
  val in_scope : Name.t -> ty param -> 'a m -> 'a m
  val in_scopes : (Name.t * ty param) list -> 'a m -> 'a m
  val under_restriction : tm -> tm -> 'a m -> 'a m

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
        let vtm = T.Cx.eval T.Cx.emp tm in
        let tm = T.Cx.quote T.Cx.emp ~ty:vty vtm in
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
    C.bind (print_diagnostics w) @@ fun _ ->
    ret a


  let under_restriction = C.under_restriction
  let in_scopes = C.in_scopes
  let in_scope = C.in_scope


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
    | Emp -> go_globals renv @@ T.bindings env
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
  M.ret @@ go_locals ResEnv.init psi


let should_split_ext_bnd ebnd =
  match ebnd with
  | Tm.NB ([_], (_, [])) -> false
  | _ -> true


let split_ext_bnd ebnd =
  let xs, ty, sys = Tm.unbind_ext ebnd in
  let rec go xs =
    match xs with
    | [] ->
      Tm.make @@ Tm.Rst {ty; sys}
    | x :: xs ->
      let ty' = go xs in
      Tm.make @@ Tm.Ext (Tm.bind_ext (Emp #< x) ty' [])
  in
  let ty = go @@ Bwd.to_list xs in
  List.map Name.name (Bwd.to_list xs), ty



let normalize_ty ty =
  M.lift C.typechecker >>= fun (module T) ->
  let vty = T.Cx.eval T.Cx.emp ty in
  M.ret @@ T.Cx.quote_ty T.Cx.emp vty

let rec elab_sig env =
  function
  | [] ->
    M.ret ()
  | dcl :: esig ->
    elab_decl env dcl >>= fun env' ->
    M.lift C.go_to_top >> (* This is suspicious, in connection with the other suspicious thing ;-) *)
    M.lift (U.ambulando @@ Name.fresh ()) >>
    elab_sig env' esig


and elab_decl env =
  function
  | E.Define (name, scheme, e) ->
    elab_scheme env scheme @@ fun cod ->
    elab_chk env cod e >>= fun tm ->
    let alpha = Name.named @@ Some name in

    M.lift C.ask >>= fun psi ->
    M.lift @@ U.define psi alpha cod tm >>
    M.ret @@ T.add name alpha env

  | E.Debug filter ->
    let title =
      match filter with
      | `All -> "Development state:"
      | `Constraints -> "Unsolved constraints:"
    in
    M.lift @@ C.dump_state Format.std_formatter title filter >>
    M.ret env

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
  M.lift @@ U.guess psi ~ty0:rty ~ty1:ty tm C.ret >>= fun tm' ->
  M.lift C.go_to_bottom >> (* This is suspicious ! *)
  M.ret tm'

and elab_chk env ty e : tm M.m =
  match Tm.unleash ty, e with
  | Tm.Rst info, _ ->
    elab_chk env info.ty e >>=
    guess_restricted info.ty info.sys

  | _, E.Quo tmfam ->
    get_resolver env >>= fun renv ->
    M.ret @@ tmfam renv


  | _, E.Lam ([], e) ->
    elab_chk env ty e

  | Tm.Pi (dom, cod), E.Lam (name :: names, e) ->
    let x = Name.named @@ Some name in
    let codx = Tm.unbind_with x (fun _ -> `Only) cod in
    M.in_scope x (`P dom) begin
      elab_chk env codx @@
      E.Lam (names, e)
    end >>= fun bdyx ->
    M.ret @@ Tm.make @@ Tm.Lam (Tm.bind x bdyx)


  | Tm.Ext (Tm.NB ([_], (cod, []))), E.Lam (name :: names, e) ->
    let x = Name.named @@ Some name in
    let codx = Tm.open_var 0 x (fun _ -> `Only) cod in
    M.in_scope x `I begin
      elab_chk env codx @@
      E.Lam (names, e)
    end >>= fun bdyx ->
    M.ret @@ Tm.make @@ Tm.ExtLam (Tm.bindn (Emp #< x) bdyx)

  | Tm.Ext ebnd, e when should_split_ext_bnd ebnd->
    let names, ety = split_ext_bnd ebnd in
    elab_chk env ety e >>= fun tm ->
    let bdy =
      let xs = List.map Name.named names in
      Tm.bindn (Bwd.from_list xs) @@
      let hd = Tm.Down {ty = ety; tm = tm} in
      let args = List.map (fun x -> Tm.ExtApp [Tm.up (Tm.Ref (x, `Only), Emp)]) xs in
      let spine = Emp <>< args in
      Tm.up (hd, spine)
    in
    M.ret @@ Tm.make @@ Tm.ExtLam bdy



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
    M.lift @@ U.hole psi ty C.ret >>= fun tm ->
    M.lift C.go_right >>
    M.emit @@ M.UserHole {name; ty; tele = psi; tm = Tm.up tm} >>
    M.ret @@ Tm.up tm

  | _ ->
    failwith "TODO"


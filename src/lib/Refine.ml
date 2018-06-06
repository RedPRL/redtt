(* Experimental code *)

open Unify open Dev open Contextual open RedBasis open Bwd open BwdNotation
module Notation = Monad.Notation (Contextual)
open Notation

module T = Map.Make (String)

type edecl =
  | Make of string * escheme
  | Refine of string * echk
  | Debug

and escheme = echk

and echk =
  | Hole
  | Lam of string * echk
  | Pair of echk * echk
  | Type
  | Quo of (ResEnv.t -> tm)
  | Up of einf

and einf =
  | Var of string

(* e-sigarette ;-) *)
type esig =
  edecl list

let univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kind.Pre

let get_tele =
  ask >>= fun psi ->
  let go (x, p) =
    match p with
    | `P ty -> x, ty
    | _ -> failwith "get_tele"
  in
  ret @@ Bwd.map go psi

let get_resolver env =
  let rec go_globals renv  =
    function
    | [] -> renv
    | (name, (x, _, _)) :: env ->
      let renvx = ResEnv.global name x renv in
      go_globals renvx env
  in
  let rec go_locals renv =
    function
    | Emp -> go_globals renv @@ T.bindings env
    | Snoc (psi, (x, _)) ->
      let renvx = ResEnv.global (Name.to_string x) x renv in
      go_locals renvx psi
  in
  ask >>= fun psi ->
  ret @@ go_locals ResEnv.init psi


type goal = {ty : ty; tm : tm}

let solve goal tm =
  active @@ Unify {ty0 = goal.ty; ty1 = goal.ty; tm0 = goal.tm; tm1 = tm}


let rec elab_sig env =
  function
  | [] ->
    ret ()
  | dcl :: esig ->
    elab_decl env dcl >>= fun env' ->
    ambulando (Name.fresh ()) >>
    elab_sig env' esig

and elab_decl env =
  function
  | Make (name, scheme) ->
    hole Emp univ @@ fun ty ->
    hole Emp (Tm.up ty) @@ fun tm ->
    elab_scheme env (Tm.up ty) scheme >>
    let alpha = Name.named @@ Some name in
    define Emp alpha (Tm.up ty) (Tm.up tm) >>
    ret @@ T.add name (alpha, ty, tm) env

  | Refine (name, e) ->
    typechecker >>= fun (module Ty) ->
    begin
      match T.find_opt name env with
      | Some (_, ty, tm) ->
        let vty = Ty.Cx.eval Ty.Cx.emp @@ Tm.up ty in
        let ty = Ty.Cx.quote_ty Ty.Cx.emp vty in
        elab_chk env {ty; tm = Tm.up tm} e >>
        ret env
      | None ->
        failwith "Refine"
    end

  | Debug ->
    dump_state Format.std_formatter "debug" >>
    ret env


and elab_scheme env tm scheme =
  elab_chk env {ty = univ; tm} scheme


and make_pair goal kont =
  match Tm.unleash goal.ty with
  | Tm.Sg (dom, cod) ->
    get_tele >>= fun psi ->
    hole psi dom @@ fun tm0 ->
    typechecker >>= fun (module T) ->
    let module HS = HSubst (T) in
    let vdom = T.Cx.eval T.Cx.emp dom in
    let cod' = HS.inst_ty_bnd cod (vdom, Tm.up tm0) in
    hole psi cod' @@ fun tm1 ->
    kont {ty = dom; tm = Tm.up tm0} {ty = cod'; tm = Tm.up tm1} >>
    solve goal @@ Tm.cons (Tm.up tm0) (Tm.up tm1)
  | _ ->
    failwith "make_pair"

and make_lambda name goal kont =
  match Tm.unleash goal.ty with
  | Tm.Pi (dom, cod) ->
    get_tele >>= fun psi ->
    let x = Name.named @@ Some name in
    let codx = Tm.unbind_with x (fun _ -> `Only) cod in
    hole (psi #< (x, dom)) codx @@ fun bdyx ->
    in_scope x (`P dom) begin
      kont {ty = codx; tm = Tm.up bdyx}
    end >>
    solve goal @@ Tm.make @@ Tm.Lam (Tm.bind x @@ Tm.up bdyx)

  | _ ->
    Format.eprintf "lambda failed: %a@." (Tm.pp Pretty.Env.emp) goal.ty;
    failwith "lambda"

and make_pi name goal kdom kcod =
  match Tm.unleash goal.ty with
  | Tm.Univ _ ->
    get_tele >>= fun psi ->
    hole psi univ @@ fun dom->
    let x = Name.named @@ Some name in
    hole (psi #< (x, Tm.up dom)) univ @@ fun codx ->
    kdom {ty = univ; tm = Tm.up dom} >>
    in_scope x (`P (Tm.up dom)) begin
      kcod {ty = univ; tm = Tm.up codx}
    end >>
    solve goal @@ Tm.make @@ Tm.Pi (Tm.up dom, Tm.bind x @@ Tm.up codx)

  | _ ->
    failwith "make_pi"


and elab_chk env (goal : goal) =
  function
  | Type ->
    solve goal @@ Tm.univ ~lvl:(Lvl.Const 0) ~kind:Kind.Kan

  | Pair (e0, e1) ->
    make_pair goal @@ fun goal0 goal1 ->
    elab_chk env goal0 e0 >>
    elab_chk env goal1 e1

  | Lam (name, e) ->
    make_lambda name goal @@ fun goal_bdy ->
    elab_chk env goal_bdy e

  | Quo tmfam ->
    get_resolver env >>= fun renv ->
    solve goal @@ tmfam renv

  | Up inf ->
    elab_inf env goal inf

  | Hole ->
    ret ()

and elab_inf env goal =
  function
  | Var name ->
    get_resolver env >>= fun renv ->
    begin
      match ResEnv.get name renv with
      | `Ref a ->
        lookup_var a `Only >>= fun ty ->
        active @@ Unify {ty0 = goal.ty; ty1 = ty; tm0 = goal.tm; tm1 = Tm.up (Tm.Ref (a, `Only), Emp)}
      | _ -> failwith "var"
    end


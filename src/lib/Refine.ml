(* Experimental code *)

open Unify open Dev open Contextual open RedBasis open Bwd
module Notation = Monad.Notation (Contextual)
open Notation

module E = ESig

module T = Map.Make (String)


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


type goal = {ty : ty; sys : (tm, tm) Tm.system}


let rec pp_tele fmt =
  function
  | Emp ->
    ()

  | Snoc (Emp, (x, ty)) ->
    Format.fprintf fmt "%a : %a"
      Name.pp x
      (Tm.pp Pretty.Env.emp) ty

  | Snoc (tele, (x, ty)) ->
    Format.fprintf fmt "%a, %a : %a"
      pp_tele tele
      Name.pp x
      (Tm.pp Pretty.Env.emp) ty

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
  | E.Define (name, scheme, e) ->
    elab_scheme env scheme >>= fun sch ->
    elab_chk env {ty = sch; sys = []} e >>= fun tm ->
    let alpha = Name.named @@ Some name in
    define Emp alpha sch tm >>
    ret @@ T.add name (alpha, sch, tm) env

  | E.Debug ->
    dump_state Format.std_formatter "debug" >>
    ret env

and elab_scheme env scheme =
  elab_chk env {ty = univ; sys = []} scheme

and elab_chk env {ty; _} : E.echk -> tm m =
  function
  | E.Quo tmfam ->
    get_resolver env >>= fun renv ->
    (* TODO: unify with boundary *)
    ret @@ tmfam renv

  | E.Hole ->
    get_tele >>= fun psi ->
    begin
      Format.printf "Hole:@ @[<1>%a %a %a@]@."
        pp_tele psi
        Uuseg_string.pp_utf_8 "⊢"
        (Tm.pp Pretty.Env.emp) ty;

      hole psi ty @@ fun tm -> ret tm
    end >>= fun tm ->
    go_right >>
    ret @@ Tm.up tm

  | E.Lam (name, e) ->
    let x = Name.named @@ Some name in
    begin
      match Tm.unleash ty with
      | Tm.Pi (dom, cod) ->
        let codx = Tm.unbind_with x (fun _ -> `Only) cod in
        in_scope x (`P dom) begin
          elab_chk env {ty = codx; sys = []} e
        end >>= fun bdyx ->
        ret @@ Tm.make @@ Tm.Lam (Tm.bind x bdyx)

      | _ ->
        failwith "lam"
    end

  | Pair (e0, e1) ->
    begin
      match Tm.unleash ty with
      | Tm.Sg (dom, cod) ->
        elab_chk env {ty = dom; sys = []} e0 >>= fun tm0 ->
        typechecker >>= fun (module T) ->
        let module HS = HSubst (T) in
        let vdom = T.Cx.eval T.Cx.emp dom in
        let cod' = HS.inst_ty_bnd cod (vdom, tm0) in
        elab_chk env {ty = cod'; sys = []} e1 >>= fun tm1 ->
        ret @@ Tm.cons tm0 tm1

      | _ ->
        failwith "pair"
    end

  | _ ->
    failwith "TODO"


(* solve goal @@ Tm.univ ~lvl:(Lvl.Const 0) ~kind:Kind.Kan *)

(* | Pair (e0, e1) ->
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
   ret () *)

(* and elab_inf env goal =
   function
   | Var name ->
    get_resolver env >>= fun renv ->
    begin
      match ResEnv.get name renv with
      | `Ref a ->
        lookup_var a `Only >>= fun ty ->
        active @@ Unify {ty0 = goal.ty; ty1 = ty; tm0 = goal.tm; tm1 = Tm.up (Tm.Ref (a, `Only), Emp)}
      | _ -> failwith "var"
    end *)


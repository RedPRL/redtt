(* Experimental code *)

open Unify open Dev open Contextual open RedBasis open Bwd open BwdNotation
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
    | (name, x) :: env ->
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

  | Snoc (Emp, (x, cell)) ->
    pp_tele_cell fmt (x, cell)

  | Snoc (tele, (x, cell)) ->
    Format.fprintf fmt "%a,@,@,%a"
      pp_tele tele
      pp_tele_cell (x, cell)

and pp_tele_cell fmt (x, cell) =
  match cell with
  | `P ty ->
    Format.fprintf fmt "@[<1>%a : %a@]"
      Name.pp x
      (Tm.pp Pretty.Env.emp) ty

  | `Tw (ty0, ty1) ->
    Format.fprintf fmt "@[<1>%a : %a | %a@]"
      Name.pp x
      (Tm.pp Pretty.Env.emp) ty0
      (Tm.pp Pretty.Env.emp) ty1

  | `I ->
    Format.fprintf fmt "@[<1>%a : dim@]"
      Name.pp x

  | `R (r0, r1) ->
    Format.fprintf fmt "@[<1>%a = %a@]"
      (Tm.pp Pretty.Env.emp) r0
      (Tm.pp Pretty.Env.emp) r1


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
    elab_scheme env scheme @@ fun cod ->
    elab_chk env {ty = cod; sys = []} e >>= fun tm ->
    let alpha = Name.named @@ Some name in

    ask >>= fun psi ->
    define psi alpha cod tm >>
    ret @@ T.add name alpha env

  | E.Debug ->
    dump_state Format.std_formatter "debug" >>
    ret env

and elab_scheme env (cells, ecod) kont =
  let rec go gm =
    function
    | [] ->
      elab_chk env {ty = univ; sys = []} ecod >>= fun cod ->
      kont cod
    | (name, edom) :: cells ->
      elab_chk env {ty = univ; sys = []} edom >>= fun dom ->
      let x = Name.named @@ Some name in
      in_scope x (`P dom) @@
      go (gm #< (x, dom)) cells
  in
  go Emp cells

and elab_chk env {ty; _} : E.echk -> tm m =
  function
  | E.Quo tmfam ->
    get_resolver env >>= fun renv ->
    (* TODO: unify with boundary *)
    ret @@ tmfam renv

  | E.Hole name ->
    ask >>= fun psi ->
    begin
      Format.printf "?%s:@, @[<v>@[<v>%a@]@;%a@,%a@]@."
        (match name with Some s -> s | None -> "Hole")
        pp_tele psi
        Uuseg_string.pp_utf_8 "⊢"
        (Tm.pp Pretty.Env.emp) ty;

      hole psi ty @@ fun tm -> ret tm
    end >>= fun tm ->
    go_right >>
    ret @@ Tm.up tm

  | E.Lam (names, e) ->
    begin
      match names with
      | [] ->
        elab_chk env {ty; sys = []} e
      | name :: names ->
        let x = Name.named @@ Some name in
        match Tm.unleash ty with
        | Tm.Pi (dom, cod) ->
          let codx = Tm.unbind_with x (fun _ -> `Only) cod in
          in_scope x (`P dom) begin
            elab_chk env {ty = codx; sys = []} @@
            E.Lam (names, e)
          end >>= fun bdyx ->
          ret @@ Tm.make @@ Tm.Lam (Tm.bind x bdyx)

        | _ ->
          failwith "lam"
    end

  | Tuple es ->
    begin
      match es with
      | [] ->
        failwith "empty tuple"
      | [e] ->
        elab_chk env {ty; sys = []} e
      | e :: es ->
        begin
          match Tm.unleash ty with
          | Tm.Sg (dom, cod) ->
            elab_chk env {ty = dom; sys = []} e >>= fun tm0 ->
            typechecker >>= fun (module T) ->
            let module HS = HSubst (T) in
            let vdom = T.Cx.eval T.Cx.emp dom in
            let cod' = HS.inst_ty_bnd cod (vdom, tm0) in
            elab_chk env {ty = cod'; sys = []} (Tuple es) >>= fun tm1 ->
            ret @@ Tm.cons tm0 tm1
          | _ ->
            failwith "pair"
        end
    end

  | Type ->
    begin
      match Tm.unleash ty with
      | Tm.Univ _ ->
        ret @@ Tm.univ ~kind:Kind.Kan ~lvl:(Lvl.Const 0)
      | _ ->
        failwith "Type"
    end


  | _ ->
    failwith "TODO"

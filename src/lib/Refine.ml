(* Experimental code *)

open Unify open Dev open Contextual open RedBasis open Bwd open BwdNotation
module Notation = Monad.Notation (Contextual)
open Notation

type goal =
  {ty : ty;
   lbl : string;
   args : (ty * tm) list;
   solve : tm -> unit m;
   abort : unit m;
   subgoal : string -> telescope -> ty -> (tm Tm.cmd -> unit m) -> unit m}

let pop_goal =
  popr >>= function
  | E (alpha, ty, Hole) as e ->
    let gm, cod = telescope ty in
    begin
      match Tm.unleash cod with
      | Tm.LblTy info ->
        let solve tm = define gm alpha ~ty:cod @@ Tm.make @@ Tm.LblRet tm in
        let subgoal lbl gm' ty kont =
          let ty' = Tm.make @@ Tm.LblTy {lbl; args = []; ty} in
          hole (gm <.> gm') ty' @@ fun (hd, sp) ->
          kont @@ (hd, sp #< Tm.LblCall)
        in
        let abort = pushr e in
        ret {ty = info.ty; lbl = info.lbl; args = info.args; solve; subgoal; abort}
      | _ ->
        failwith "pop_goal"
    end
  | _ -> failwith "No hole"

let push_goal lbl gm ty kont =
  let ty' = Tm.make @@ Tm.LblTy {lbl; args = []; ty} in
  hole gm ty' kont

let refine_pair =
  pop_goal >>= fun goal ->
  match Tm.unleash goal.ty with
  | Tm.Sg (dom, Tm.B (_, cod)) ->
    goal.subgoal "proj0" Emp dom @@ fun proj0 ->
    let cod' = Tm.subst (Tm.Sub (Tm.Id, proj0)) cod in
    goal.subgoal "proj1" Emp cod' @@ fun proj1 ->
    goal.solve @@ Tm.cons (Tm.up proj0) (Tm.up proj1)
  | _ ->
    failwith "refine_pair"

let refine_tt =
  pop_goal >>= fun goal ->
  match Tm.unleash goal.ty with
  | Tm.Bool ->
    goal.solve @@ Tm.make Tm.Tt
  | _ ->
    failwith "refine_tt"

let refine_ff =
  pop_goal >>= fun goal ->
  match Tm.unleash goal.ty with
  | Tm.Bool ->
    goal.solve @@ Tm.make Tm.Ff
  | _ ->
    failwith "refine_ff"

let unify_ty ty0 ty1 =
  let univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kind.Pre in
  let brack = Name.fresh () in
  pushr @@ Bracket brack >>
  active @@ Unify {ty0 = univ; ty1 = univ; tm0 = ty0; tm1 = ty1} >>
  go_to_top >>
  ambulando brack


(* Just to test the unifier *)
let soft_ff =
  pop_goal >>= fun goal ->
  unify_ty goal.ty @@ Tm.make Tm.Bool >>
  goal.solve @@ Tm.make Tm.Ff


let refine_lam x =
  pop_goal >>= fun goal ->
  match Tm.unleash goal.ty with
  | Tm.Pi (dom, cod) ->
    let codx = Tm.unbind_with x `Only cod in
    goal.subgoal "body" (Emp #< (x, dom)) codx @@ fun bdyx ->
    goal.solve @@ Tm.make @@ Tm.Lam (Tm.bind x @@ Tm.up bdyx)
  | _ ->
    failwith "refine_lam"


module SourceLang =
struct

  type edecl =
    | Make of string * eterm
    | Refine of elhs * egadget
    | Debug of string

  and egadget =
    | Ret of eterm

  and eterm =
    | Hole
    | Lam of string * eterm
    | Pair of eterm * eterm
    | Quo of (ResEnv.t -> tm)

  and elhs = string * epat list

  and epat =
    | PVar of string

  type esig =
    edecl list

  let make_goal_ty lbl ty =
    Tm.make @@ Tm.LblTy {lbl; args = []; ty}

  let push_program name =
    let x = Name.fresh () in
    let univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kind.Pre in
    begin
      hole Emp (make_goal_ty (name ^ ".type") univ) @@ fun (hd, sp) ->
      hole_named x Emp (make_goal_ty name @@ Tm.up (hd, sp #< Tm.LblCall)) @@ fun _ -> ret ()
    end >>
    ret x

  let rec elab_sig renv =
    function
    | [] ->
      ret ()

    | Make (name, eterm) :: esig ->
      push_program name >>= fun x ->
      elab_term renv eterm >>
      go_right >>
      let renvx = ResEnv.global name x renv in
      elab_sig renvx esig

    | Refine (lhs, gadg) :: esig ->
      elab_lhs renv lhs >>= fun renv' ->
      elab_gadget renv' gadg >>
      go_right >>
      elab_sig renv esig

    | Debug msg :: esig ->
      dump_state Format.std_formatter msg >>
      elab_sig renv esig

  and elab_lhs renv (lbl, pats) =
    pop_goal >>= fun goal ->
    if lbl = goal.lbl then
      goal.abort >>
      elab_pats renv (pats, goal.args)
    else
      failwith "goal label mismatch"

  and elab_pats renv (pats, args) =
    match pats, args with
    | [], [] ->
      ret renv

    | PVar name :: pats, (ty, tm) :: args ->
      (* Untested *)
      let x = Name.named @@ Some name in
      let renvx = ResEnv.global name x renv in
      define Emp x ~ty tm >>
      go_right >>
      elab_pats renvx (pats, args)

    | _ ->
      failwith "TODO"

  and elab_gadget renv =
    function
    | Ret e ->
      elab_term renv e

  and elab_term renv =
    function
    | Hole ->
      ret ()
    | Quo fam ->
      let tm = fam renv in
      pop_goal >>= fun goal ->
      goal.solve tm
    | Lam (name, e) ->
      let x = Name.named @@ Some name in
      let renvx = ResEnv.global name x renv in
      refine_lam x >>
      elab_term renvx e
    | Pair (e0, e1) ->
      refine_pair >>
      elab_term renv e0 >>
      go_right >>
      elab_term renv e1

  let test_script =
    elab_sig ResEnv.init
      [ Make ("foo", Quo (fun _ -> Tm.make Tm.Bool))
      ; Debug "test0"
      ; Refine (("foo", []), Ret Hole)
      ; Debug "test1"
      ; Make ("bar", Hole)
      ; Debug "test2"
      ]

end

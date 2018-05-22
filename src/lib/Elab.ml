open RedBasis
open Dev

type eterm =
  | Lambda of string list * eterm
  | Pi of (string * eterm) * eterm
  | Pair of eterm * eterm
  | Hole of string
  | Tt

module M = DevMonad
include (IxMonad.Notation (M))

let solve_guess_node m =
  M.push_cell >>
  M.push_guess >>
  m >>
  M.pop_guess >>
  M.solve >>
  M.pop_cell

let under_node m =
  M.down >>
  m >>
  M.up

module Refine :
sig
  val pi : string option -> (dev, dev) M.move
  val pair : (dev, dev) M.move
end =
struct

  let map_sys f =
    List.map (fun (r, r', otm) -> r, r', Option.map f otm)

  let pi_get_dom tm =
    match Tm.unleash tm with
    | Tm.Pi (dom, _) -> dom
    | _ -> failwith "pi_get_dom"

  let pi_get_cod tm =
    match Tm.unleash tm with
    | Tm.Pi (_, Tm.B (_, cod)) -> cod
    | _ -> failwith "pi_get_cod"

  let pi nm : (dev, dev) M.move =
    M.get_hole >>= fun (_, goal) ->
    match Tm.unleash goal.ty with
    | Tm.Univ univ ->
      M.freeze goal >>= fun fgoal ->
      M.claim_with None {ty = goal.ty; sys = map_sys pi_get_dom goal.sys} @@ fun alpha ->
      begin
        M.defrost_tm alpha >>= fun dom ->
        M.ret @@ Tm.Macro.arr (Tm.up dom) @@ Tm.univ ~kind:univ.kind ~lvl:univ.lvl
      end >>= fun fam_ty ->
      begin
        M.defrost_rty fgoal >>= fun {sys; _} ->
        let fam_face tm = Tm.lam nm @@ pi_get_cod tm in
        M.ret @@ map_sys fam_face sys
      end >>= fun fam_sys ->
      M.claim_with (Some "fam") {ty = fam_ty; sys = fam_sys} @@ fun beta ->
      M.defrost_tm alpha >>= fun dom ->
      M.defrost_tm beta >>= fun cod_fam ->
      M.fill_hole @@
      Tm.pi nm (Tm.up dom) @@
      Tm.up @@ Tm.make @@ Tm.FunApp (Tm.subst Tm.Proj cod_fam, Tm.up @@ Tm.var 0)
    | _ ->
      failwith "pi: expected universe"

  let pair =
    M.get_hole >>= fun (_, goal) ->
    match Tm.unleash goal.ty with
    | Tm.Sg (dom, Tm.B (nm, cod)) ->
      M.freeze goal >>= fun fgoal ->
      begin
        let car_face tm = Tm.up @@ Tm.car @@ Tm.down ~ty:goal.ty ~tm in
        M.ret @@ map_sys car_face goal.sys
      end >>= fun car_sys ->
      M.claim_with nm {ty = dom; sys = car_sys} @@ fun alpha ->
      begin
        M.defrost_rty fgoal >>= fun {sys; ty} ->
        let cdr_face tm = Tm.up @@ Tm.cdr @@ Tm.down ~ty ~tm in
        M.ret @@ map_sys cdr_face sys
      end >>= fun cdr_sys ->
      M.claim_with nm {ty = cod; sys = cdr_sys} @@ fun beta ->
      M.defrost_tm alpha >>= fun tm0 ->
      M.defrost_tm beta >>= fun tm1 ->
      M.fill_hole @@ Tm.cons (Tm.up tm0) (Tm.up tm1)
    | _ ->
      failwith "pair: expected sg type"
end

let rec elab : eterm -> (dev, dev) M.move =
  function
  | Tt ->
    M.fill_hole @@ Tm.make Tm.Tt

  | Hole str ->
    M.user_hole str

  | Pair (e0, e1) ->
    Refine.pair >>
    solve_guess_node (elab e0) >>
    under_node @@
    solve_guess_node (elab e1)

  | Lambda (xs, etm) ->
    let rec go =
      function
      | [] -> elab etm
      | x::xs ->
        M.lambda (Some x) >>
        under_node @@ go xs
    in go xs

  | Pi ((x, dom), cod) ->
    Refine.pi (Some x) >>
    solve_guess_node (elab dom) >>
    under_node @@
    solve_guess_node @@
    begin
      M.lambda (Some x) >>
      under_node @@ elab cod
    end

let test_script = elab @@ Lambda (["y"; "x"], Pair (Pi (("z", Hole "?0"), Hole "?01"), Hole "?1"))

let bool = Tm.make Tm.Bool
let test_ty = Tm.pi None bool @@ Tm.pi None bool @@ Tm.sg None (Tm.univ Kind.Kan (Lvl.Const 0)) bool
let foo () =
  let tm = M.run test_ty test_script in
  Format.printf "Result: %a@." (Tm.pp Pretty.Env.emp) tm

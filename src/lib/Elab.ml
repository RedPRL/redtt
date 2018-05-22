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

  let unleash_rty rty =
    M.defrost_rty rty >>= fun {ty; _} ->
    M.ret @@ Tm.unleash ty

  let pi nm : (dev, dev) M.move =
    M.get_hole >>= fun (_, goal) ->
    unleash_rty goal >>=
    function
    | Tm.Univ _ ->
      begin
        M.defrost_rty goal >>= fun {ty; sys} ->
        M.ret @@ {ty; sys = map_sys pi_get_dom sys}
      end >>= fun dom_goal ->
      M.claim_with None dom_goal @@ fun alpha ->
      begin
        M.defrost_tm alpha >>= fun dom ->
        M.defrost_rty goal >>= fun {ty; sys} ->
        let fam_face tm = Tm.lam nm @@ pi_get_cod tm in
        let fam_ty = Tm.Macro.arr (Tm.up dom) ty in
        let fam_sys = map_sys fam_face sys in
        M.ret {ty = fam_ty; sys = fam_sys}
      end >>= fun fam_goal ->
      M.claim_with (Some "fam") fam_goal @@ fun beta ->
      M.defrost_tm alpha >>= fun dom ->
      M.defrost_tm beta >>= fun cod_fam ->
      M.fill_hole @@
      Tm.pi nm (Tm.up dom) @@
      Tm.up @@ Tm.make @@ Tm.FunApp (Tm.subst Tm.Proj cod_fam, Tm.up @@ Tm.var 0)
    | _ ->
      failwith "pi: expected universe"

  let pair =
    M.get_hole >>= fun (_, goal) ->
    M.defrost_rty goal >>= fun {ty; sys} ->
    match Tm.unleash ty with
    | Tm.Sg (dom, Tm.B (nm, cod)) ->
      begin
        let car_face tm = Tm.up @@ Tm.car @@ Tm.down ~ty ~tm in
        let car_sys = map_sys car_face sys in
        M.ret {ty = dom; sys = car_sys}
      end >>= fun car_goal ->
      M.claim_with nm car_goal @@ fun alpha ->
      begin
        M.defrost_rty goal >>= fun {sys; ty} ->
        let cdr_face tm = Tm.up @@ Tm.cdr @@ Tm.down ~ty ~tm in
        M.ret {ty = cod; sys = map_sys cdr_face sys}
      end >>= fun cdr_goal ->
      M.claim_with nm cdr_goal @@ fun beta ->
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

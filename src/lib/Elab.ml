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

let claim_with nm ty m =
  M.claim nm ty >>
  under_node m

module Refine =
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
    | Tm.Univ _ ->
      claim_with None {ty = goal.ty; sys = map_sys pi_get_dom goal.sys} begin
        let fam_ty = Tm.pi nm (Tm.up @@ Tm.var 0) goal.ty in
        let fam_sys =
          let fam_face tm = Tm.lam nm @@ pi_get_cod tm in
          map_sys fam_face @@ Tm.subst_sys Tm.Proj goal.sys
        in
        claim_with (Some "fam") {ty = fam_ty; sys = fam_sys} begin
          let pi_ty =
            Tm.pi nm (Tm.up @@ Tm.var 1) @@
            Tm.up @@ Tm.make @@ Tm.FunApp (Tm.var 1, Tm.up @@ Tm.var 0)
          in
          M.fill_hole pi_ty
        end
      end
    | _ ->
      failwith "pi: expected universe"

  let pair =
    M.get_hole >>= fun (_, goal) ->
    match Tm.unleash goal.ty with
    | Tm.Sg (dom, Tm.B (nm, cod)) ->
      let car_sys =
        let car_face tm = Tm.up @@ Tm.car @@ Tm.down ~ty:goal.ty ~tm in
        map_sys car_face goal.sys
      in
      claim_with nm {ty = dom; sys = car_sys} begin
        let cdr_sys =
          let cdr_face tm = Tm.up @@ Tm.cdr @@ Tm.down ~ty:(Tm.subst Tm.Proj goal.ty) ~tm in
          map_sys cdr_face @@ Tm.subst_sys Tm.Proj goal.sys
        in
        claim_with None {ty = cod; sys = cdr_sys} begin
          M.fill_hole @@ Tm.cons (Tm.up @@ Tm.var 1) (Tm.up @@ Tm.var 0)
        end
      end
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

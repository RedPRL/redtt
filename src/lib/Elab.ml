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

let rec elab : eterm -> (dev, dev) M.move =
  function
  | Tt ->
    M.fill_hole @@ Tm.make Tm.Tt

  | Hole str ->
    M.user_hole str

  | Pair (e0, e1) ->
    M.pair >>
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
    M.pi (Some x) >>
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

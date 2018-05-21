type ty = Tm.chk Tm.t
type tm = Tm.chk Tm.t

(** TODO: I think it might make sense to consider a version where the content of the cell (is it a guess or a let, etc.) is
    held as a reference to something in the proof state, rather in the dev term itself. This would give us a way to implement
    tactics that do complicated stuff to the global proof state without needing to remember how to get to one place or another in the zipper. *)

type cell =
  | Guess of {nm : string option; ty : ty; guess : dev}
  | Let of {nm : string option; ty : ty; def : tm}
  | Lam of {nm : string option; ty : ty}

and dev =
  | Hole of ty (* TODO: add boundary *)
  | Node of cell * dev
  | Ret of tm

(** Given a {e pure} development calculus term (one which has no holes), return a core language term. *)
let rec extract : dev -> tm =
  function
  | Hole _ ->
    failwith "extract: encountered impure development term (Hole)"
  | Node (cell, dev) ->
    begin
      match cell with
      | Guess _ ->
        failwith "extract: encountered impure development term (Guess)"
      | Lam {nm; _} ->
        Tm.lam nm @@ extract dev
      | Let {ty; def; nm} ->
        let tm = Tm.make @@ Tm.Down {ty; tm = def} in
        Tm.let_ nm tm @@ extract dev
    end
  | Ret tm ->
    tm


let rec ppenv_cell env =
  function
  | Guess {nm; _} ->
    let _, envx = Pretty.Env.bind nm env in
    envx
  | Let {nm; _} ->
    let _, envx = Pretty.Env.bind nm env in
    envx
  | Lam {nm; _} ->
    let _, envx = Pretty.Env.bind nm env in
    envx

let rec pp_cell env fmt cell =
  let env' = ppenv_cell env cell in
  match cell with
  | Guess {ty; guess; _} ->
    let x = Pretty.Env.var 0 env' in
    begin
      match guess with
      | Hole _ ->
        Format.fprintf fmt "?%a : %a"
          Uuseg_string.pp_utf_8 x
          (Tm.pp env) ty
      | _ ->
        Format.fprintf fmt "?%a : %a %a %a"
          Uuseg_string.pp_utf_8 x
          (Tm.pp env) ty
          Uuseg_string.pp_utf_8 "▷"
          (pp_dev env) guess
    end

  | Let {ty; def; _} ->
    let x = Pretty.Env.var 0 env' in
    Format.fprintf fmt "!%a : %a %a %a"
      Uuseg_string.pp_utf_8 x
      (Tm.pp env) ty
      Uuseg_string.pp_utf_8 "▷"
      (Tm.pp env) def

  | Lam {ty; _} ->
    let x = Pretty.Env.var 0 env' in
    Format.fprintf fmt "λ%a : %a"
      Uuseg_string.pp_utf_8 x
      (Tm.pp env) ty

and pp_dev env fmt =
  function
  | Hole _ ->
    Format.fprintf fmt "?"
  | Ret tm ->
    Format.fprintf fmt "`%a"
      (Tm.pp env) tm
  | Node (cell, dev) ->
    let env' = ppenv_cell env cell in
    Format.fprintf fmt "%a. %a"
      (pp_cell env) cell
      (pp_dev env') dev


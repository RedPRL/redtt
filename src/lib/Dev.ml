type ty = Tm.chk Tm.t
type tm = Tm.chk Tm.t
type boundary = Tm.chk Tm.t Tm.system
type rty = {ty : ty; sys : boundary}

type name = string option

(** TODO: I think it might make sense to consider a version where the content of the cell (is it a guess or a let, etc.) is
    held as a reference to something in the proof state, rather in the dev term itself. This would give us a way to implement
    tactics that do complicated stuff to the global proof state without needing to remember how to get to one place or another in the zipper. *)

type cell =
  | Guess of {nm : name; ty : rty; guess : dev}
  | Let of {nm : name; ty : ty; def : tm}
  | Lam of {nm : name; ty : ty}

and dev =
  | Hole of rty
  | Node of cell * dev
  | Ret of tm

let rec subst sub =
  function
  | Hole rty ->
    let ty = Tm.subst sub rty.ty in
    let sys = Tm.subst_sys sub rty.sys in
    Hole {ty; sys}
  | Node (cell, dev) ->
    Node (subst_cell sub cell, subst sub dev)
  | Ret tm ->
    Ret (Tm.subst sub tm)

and subst_cell sub =
  function
  | Guess info ->
    let ty = Tm.subst sub info.ty.ty in
    let sys = Tm.subst_sys sub info.ty.sys in
    let guess = subst sub info.guess in
    Guess {info with ty = {ty; sys}; guess}
  | Let info ->
    let ty = Tm.subst sub info.ty in
    let def = Tm.subst sub info.def in
    Let {info with ty; def}
  | Lam info ->
    let ty = Tm.subst sub info.ty in
    Lam {info with ty}


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
          (pp_rty env) ty
      | _ ->
        Format.fprintf fmt "?%a : %a %a %a"
          Uuseg_string.pp_utf_8 x
          (pp_rty env) ty
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

and pp_rty env fmt rty =
  Tm.pp env fmt @@ Tm.make @@ Tm.Rst {ty = rty.ty; sys = rty.sys}

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


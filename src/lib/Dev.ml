type ty = Tm.tm
type tm = Tm.tm

module I =
struct
  type dev =
    | Ret of tm
    | Hole of ty
    | Node of cell * dev

  and cell =
    | Lam of ty
    | Guess of ty * dev
    | Let of ty * tm

  let rec close_var x k =
    function
    | Ret tm ->
      Ret (Tm.close_var x k tm)
    | Hole ty ->
      Hole (Tm.close_var x k ty)
    | Node (cell, dev) ->
      match cell with
      | Lam ty ->
        Node (Lam (Tm.close_var x k ty), close_var x (k + 1) dev)
      | Guess (ty, guess) ->
        Node (Guess (Tm.close_var x k ty, close_var x k guess), close_var x (k + 1) dev)
      | Let (ty, tm) ->
        Node (Let (Tm.close_var x k ty, Tm.close_var x k tm), close_var x (k + 1) dev)

  let rec open_var k x =
    function
    | Ret tm ->
      Ret (Tm.open_var k x tm)
    | Hole ty ->
      Hole (Tm.open_var k x ty)
    | Node (cell, dev) ->
      match cell with
      | Lam ty ->
        Node (Lam (Tm.open_var k x ty), open_var (k + 1) x dev)
      | Guess (ty, guess) ->
        Node (Guess (Tm.open_var k x ty, open_var k x guess), open_var (k + 1) x dev)
      | Let (ty, tm) ->
        Node (Let (Tm.open_var k x ty, Tm.open_var k x tm), open_var (k + 1) x dev)
end

type 'a dev_view =
  | Ret of tm
  | Hole of ty
  | Node of 'a cell_view * 'a

and 'a cell_view =
  | Lam of {x : Name.t; ty : ty}
  | Guess of {x : Name.t; ty : ty; guess : 'a}
  | Let of {x : Name.t; ty : ty; tm : tm}

type dev = I.dev
type cell = I.cell

let make : type a. dev dev_view -> dev =
  function
  | Ret tm ->
    I.Ret tm
  | Hole ty ->
    I.Hole ty
  | Node (cell, dev) ->
    match cell with
    | Lam {x; ty} ->
      I.Node (I.Lam ty, I.close_var x 0 dev)
    | Let {x; ty; tm} ->
      I.Node (I.Let (ty, tm), I.close_var x 0 dev)
    | Guess {x; ty; guess} ->
      I.Node (I.Guess (ty, guess), I.close_var x 0 dev)

let unleash : type a. dev -> dev dev_view =
  function
  | I.Ret tm ->
    Ret tm
  | I.Hole ty ->
    Hole ty
  | I.Node (cell, dev) ->
    match cell with
    | I.Lam ty ->
      let x = Name.fresh () in
      Node (Lam {x; ty}, I.open_var 0 x dev)
    | I.Let (ty, tm) ->
      let x = Name.fresh () in
      Node (Let {x; ty; tm}, I.open_var 0 x dev)
    | I.Guess (ty, guess) ->
      let x = Name.fresh () in
      Node (Guess {x; ty; guess}, I.open_var 0 x dev)

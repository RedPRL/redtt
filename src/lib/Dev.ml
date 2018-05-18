type ty = Tm.chk Tm.t
type tm = Tm.chk Tm.t
type boundary = Tm.chk Tm.t Tm.system

(** A [cell] is an entry in the development context, what Conor McBride called a {e component} in his thesis.
    These cells are also the left parts of the "binders" in the development calculus.
*)
type cell =
  | Guess of {nm : string option; ty : ty; guess : dev}
  | Let of {nm : string option; ty : ty; def : tm}
  | Lam of {nm : string option; ty : ty}
  | Constrain of boundary (* not sure if this is right *)
  | Restrict of {r : Tm.chk Tm.t; r' : Tm.chk Tm.t}

and dev =
  | Hole
  | B of cell * dev
  | Ret of tm

(** We now proceed to unleash the proof state zipper. *)

type (_, _) frame =
  | KBCell : unit * dev -> (cell, dev) frame
  | KBDev : cell * unit -> (dev, dev) frame
  | KGuess : {nm : string option; ty : ty; guess : unit} -> (dev, cell) frame

type (_, _) stack =
  | Top : ('a, 'a) stack
  | Push : ('a, 'b) frame * ('b, 'c) stack -> ('a, 'c) stack

let plug : type a b. a -> (a, b) frame -> b =
  fun a frm ->
    match frm with
    | KBCell ((), dev) ->
      B (a, dev)
    | KBDev (cell, ()) ->
      B (cell, a)
    | KGuess {nm; ty; _} ->
      Guess {nm; ty; guess = a}

let rec cut : type a b. a -> (a, b) stack -> b =
  fun a stk ->
    match stk with
    | Top -> a
    | Push (frm, stk) ->
      cut (plug a frm) stk

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
  | Constrain _ ->
    env
  | Restrict _ ->
    env

let rec pp_cell env fmt cell =
  let env' = ppenv_cell env cell in
  match cell with
  | Guess {ty; guess; _} ->
    let x = Pretty.Env.var 0 env' in
    begin
      match guess with
      | Hole ->
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

  | Constrain sys ->
    Format.fprintf fmt "constrain %a"
      (Tm.pp_sys env) sys

  | Restrict {r; r'} ->
    Format.fprintf fmt "[%a = %a]"
      (Tm.pp env) r
      (Tm.pp env) r'

and pp_dev env fmt =
  function
  | Hole ->
    Format.fprintf fmt "?"
  | Ret tm ->
    Format.fprintf fmt "`%a"
      (Tm.pp env) tm
  | B (cell, dev) ->
    let env' = ppenv_cell env cell in
    Format.fprintf fmt "%a. %a"
      (pp_cell env) cell
      (pp_dev env') dev

(** Development contexts. Following Conor McBride, we define tactics to be admissible rules
    in the theory of valid contexts. *)
module Cx :
sig
  type t
  val emp : t
  val ext : t -> cell -> t

  val pp_cx : t Pretty.t0
  val ppenv : t -> Pretty.env

  (** Compile a development context to a core-language context, for type checking.
      Guess binders turn into variable bindings (the guessed term is invisible), just like
      lambda binders. Let binders turn into definitions (which can be seen in type checking).
      Restrictions get turned into restrictions. *)
  val core : t -> Typing.cx
end =
struct
  type t =
    | Emp
    | Ext of t * cell

  let rec ppenv =
    function
    | Emp -> Pretty.Env.emp
    | Ext (cx, c) ->
      ppenv_cell (ppenv cx) c

  let rec pp_cx_ env fmt =
    function
    | Emp -> env
    | Ext (Emp, c) ->
      pp_cell env fmt c;
      ppenv_cell env c
    | Ext (t, c) ->
      let env' = pp_cx_ env fmt t in
      Format.fprintf fmt "@,";
      pp_cell env' fmt c;
      ppenv_cell env' c

  let pp_cx fmt cx =
    ignore @@ pp_cx_ Pretty.Env.emp fmt cx

  let emp = Emp
  let ext t c = Ext (t, c)

  let rec core dcx =
    match dcx with
    | Emp ->
      Typing.Cx.emp

    | Ext (dcx, c) ->
      let tcx = core dcx in
      begin
        match c with
        | Guess {ty; nm; _} ->
          let vty = Typing.Cx.eval tcx ty in
          fst @@ Typing.Cx.ext_ty tcx ~nm vty

        | Let {ty; nm; def} ->
          let vty = Typing.Cx.eval tcx ty in
          let vdef = Typing.Cx.eval tcx def in
          Typing.Cx.def tcx ~nm ~ty:vty ~el:vdef

        | Lam {ty; nm} ->
          let vty = Typing.Cx.eval tcx ty in
          fst @@ Typing.Cx.ext_ty tcx ~nm vty

        | Constrain _ ->
          tcx

        | Restrict {r; r'} ->
          let vr = Typing.Cx.eval_dim tcx r in
          let vr' = Typing.Cx.eval_dim tcx r' in
          Typing.Cx.restrict tcx vr vr'
      end
end

module IxM :
sig
  include IxMonad.S

  val down_cell : (dev, cell, unit) m
end =
struct

  type 's cmd = {foc : 's; stk : ('s, dev) stack}
  type 's state = {cx : Cx.t; ty : ty; cmd : 's cmd}

  module State = IxStateMonad.M (struct type 'i t = 'i state end)
  include State include IxMonad.Notation (State)

  exception InvalidMove

  let down_cell : (dev, cell, unit) m =
    get >>= fun state ->
    match state.cmd.foc with
    | B (cell, dev) ->
      let stk = Push (KBCell ((), dev), state.cmd.stk) in
      let cmd = {foc = cell; stk = stk} in
      set {state with cmd}

    | _ ->
      Format.eprintf "Tried to descend into %a"
        (pp_dev (Cx.ppenv state.cx))
        state.cmd.foc;
      raise InvalidMove

  let down_dev : (dev, dev, unit) m =
    get >>= fun state ->
    match state.cmd.foc with
    | B (cell, dev) ->
      let stk = Push (KBDev (cell, ()), state.cmd.stk) in
      let cmd = {foc = dev; stk = stk} in
      let cx = Cx.ext state.cx cell in
      set {state with cmd; cx}

    | _ ->
      Format.eprintf "Tried to descend into %a"
        (pp_dev (Cx.ppenv state.cx))
        state.cmd.foc;
      raise InvalidMove
end

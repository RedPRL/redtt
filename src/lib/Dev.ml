open RedBasis

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
  | Constrain of boundary
  | Restrict of {r : Tm.chk Tm.t; r' : Tm.chk Tm.t}

and dev =
  | Hole of ty
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
      | Constrain _ ->
        extract dev
      | Restrict _ ->
        extract dev
      | Let {ty; def; nm} ->
        let tm = Tm.make @@ Tm.Down {ty; tm = def} in
        Tm.let_ nm tm @@ extract dev
    end
  | Ret tm ->
    tm


(** We now proceed to unleash the proof state zipper. *)

type (_, _) frame =
  | KNodeCell : unit * dev -> (cell, dev) frame
  | KNodeDev : cell * unit -> (dev, dev) frame
  | KGuess : {nm : string option; ty : ty; guess : unit} -> (dev, cell) frame

type (_, _) stack =
  | Top : ('a, 'a) stack
  | Push : ('a, 'b) frame * ('b, 'c) stack -> ('a, 'c) stack

let plug : type a b. a -> (a, b) frame -> b =
  fun a frm ->
    match frm with
    | KNodeCell ((), dev) ->
      Node (a, dev)
    | KNodeDev (cell, ()) ->
      Node (cell, a)
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

  | Constrain sys ->
    Format.fprintf fmt "constrain %a"
      (Tm.pp_sys env) sys

  | Restrict {r; r'} ->
    Format.fprintf fmt "[%a = %a]"
      (Tm.pp env) r
      (Tm.pp env) r'

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


  exception EmptyContext
  val pop : t -> t
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

  exception EmptyContext

  let pop =
    function
    | Emp -> raise EmptyContext
    | Ext (cx, _) -> cx

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

  type ('i, 'o) move = ('i, 'o, unit) m

  val run : ty -> (dev, dev) move -> tm

  (** The names of these moves are not yet perfected. *)

  val push_guess : (cell, dev) move
  val pop_guess : (dev, cell) move

  val push_cell : (dev, cell) move
  val pop_cell : (cell, dev) move

  val down : (dev, dev) move
  val up : (dev, dev) move

  (** When the cursor is at a [Hole ty], check the supplied [tm] against [ty];
      if it matches, then replace the hole with [Ret tm]. *)
  val fill_hole : tm -> (dev, dev) move


  (** When the cursor is at a {e pure} [Guess] cell, replace it with a [Let] cell. *)
  val solve : (cell, cell) move


  (** When the cursor is at a hole of dependent function type, replace it with
      a [Lam] cell and a hole underneath it. *)
  val lambda : string option -> (dev, dev) move
end =
struct
  type 's cmd = {foc : 's; stk : ('s, dev) stack}

  (* TODO: we need a signature. *)
  type 's state = {cx : Cx.t; cmd : 's cmd}

  module State = IxStateMonad.M (struct type 'i t = 'i state end)
  include State include IxMonad.Notation (State)

  exception InvalidMove

  type ('i, 'o) move = ('i, 'o, unit) m


  let run ty m : tm =
    let init = {foc = Hole ty; stk = Top} in
    let _, final = State.run {cx = Cx.emp; cmd = init} m in
    extract final.cmd.foc

  let push_guess : _ m =
    get >>= fun state ->
    match state.cmd.foc with
    | Guess {nm; ty; guess} ->
      let stk = Push (KGuess {nm; ty; guess = ()}, state.cmd.stk) in
      let cmd = {foc = guess; stk = stk} in
      set {state with cmd}
    | _ ->
      Format.eprintf "Tried to descend into %a"
        (pp_cell (Cx.ppenv state.cx))
        state.cmd.foc;
      raise InvalidMove


  let pop_guess : (dev, cell) move =
    get >>= fun (state : dev state) ->
    match state.cmd.stk with
    | Push (KGuess {ty; nm; _}, (stk : (cell, dev) stack)) ->
      let foc = Guess {ty; nm; guess = state.cmd.foc} in
      let cmd = {foc; stk} in
      set {state with cmd}
    | _ ->
      raise InvalidMove

  let push_cell : _ m =
    get >>= fun state ->
    match state.cmd.foc with
    | Node (cell, dev) ->
      let stk = Push (KNodeCell ((), dev), state.cmd.stk) in
      let cmd = {foc = cell; stk = stk} in
      set {state with cmd}

    | _ ->
      Format.eprintf "Tried to descend into %a"
        (pp_dev (Cx.ppenv state.cx))
        state.cmd.foc;
      raise InvalidMove

  let pop_cell : (cell, dev) move =
    get >>= fun (state : cell state) ->
    match state.cmd.stk with
    | Push (KNodeCell ((), dev), (stk : (dev, dev) stack)) ->
      let foc = Node (state.cmd.foc, dev) in
      let cmd = {foc; stk} in
      set {state with cmd}

  let down : _ m =
    get >>= fun state ->
    match state.cmd.foc with
    | Node (cell, dev) ->
      let stk = Push (KNodeDev (cell, ()), state.cmd.stk) in
      let cmd = {foc = dev; stk = stk} in
      let cx = Cx.ext state.cx cell in
      set {cmd; cx}

    | _ ->
      Format.eprintf "Tried to descend into %a"
        (pp_dev (Cx.ppenv state.cx))
        state.cmd.foc;
      raise InvalidMove

  let up : (dev, dev) move =
    get >>= fun (state : dev state) ->
    match state.cmd.stk with
    | Push (KNodeDev (cell, ()), (stk : (dev, dev) stack)) ->
      let foc = Node (cell, state.cmd.foc) in
      let cmd = {foc; stk} in
      let cx = Cx.pop state.cx in
      set {cmd; cx}
    | _ ->
      raise InvalidMove


  let get_hole =
    get >>= fun state ->
    match state.cmd.foc with
    | Hole ty ->
      ret (state.cx, ty)
    | _ ->
      raise InvalidMove

  let set_foc foc =
    get >>= fun state ->
    let cmd = {state.cmd with foc} in
    set {state with cmd}


  let fill_hole tm : (dev, dev) move =
    get_hole >>= fun (cx, ty) ->
    let tcx = Cx.core cx in
    let vty = Typing.Cx.eval tcx ty in
    Typing.check tcx vty tm;
    set_foc @@ Ret tm

  let solve : (cell, cell) move =
    get >>= fun state ->
    match state.cmd.foc with
    | Guess {nm; ty; guess} ->
      let proof = extract guess in
      let tcx = Cx.core state.cx in
      let vty = Typing.Cx.eval tcx ty in
      Typing.check tcx vty proof;
      set_foc @@ Let {nm; ty; def = proof}
    | _ ->
      failwith "solve: expected guess cell"

  let lambda nm : (dev, dev) move =
    get_hole >>= fun (_, ty) ->
    match Tm.unleash ty with
    | Tm.Pi (dom, Tm.B (_, cod)) ->
      let lam = Lam {nm; ty = dom} in
      set_foc @@ Node (lam, Hole cod)
    | _ ->
      failwith "lambda: expected pi type"
end

module Test =
struct
  type eterm =
    | Lambda of string * eterm
    | Tt

  include (IxMonad.Notation (IxM))

  let rec eval : eterm -> (dev, dev) IxM.move =
    function
    | Tt ->
      IxM.fill_hole @@ Tm.make Tm.Tt

    | Lambda (x, etm) ->
      IxM.lambda (Some x) >>
      IxM.down >>
      eval etm >>
      IxM.up

  let test_script = eval @@ Lambda ("x", Tt)
  let test_ty = Tm.pi None (Tm.make Tm.Bool) (Tm.make Tm.Bool)
end

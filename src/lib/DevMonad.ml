open RedBasis
open Dev

module Cx = DevCx

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


type 's cmd = {foc : 's; stk : ('s, dev) stack}

(* TODO: add a resolver environment *)
type 's state = {gcx : GlobalCx.t; cx : Cx.t; cmd : 's cmd}

module State = IxStateMonad.M (struct type 'i t = 'i state end)
include State include IxMonad.Notation (State)

exception InvalidMove

type ('i, 'o) move = ('i, 'o, unit) m


let run ty m : tm =
  let init = {foc = Hole ty; stk = Top} in
  let _, final = State.run {gcx = GlobalCx.emp; cx = Cx.emp; cmd = init} m in
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
    set {state with cmd; cx}

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
    set {state with cmd; cx}
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

let add_hole name ~ty ~sys=
  get >>= fun state ->
  let gcx = GlobalCx.add_hole state.gcx name ~ty ~sys in
  set {state with gcx}


let check ~ty ~tm : ('i, 'i) move =
  get >>= fun state ->
  let module Sig = struct let globals = state.gcx end in
  let module T = Typing.M (Sig) in
  let tcx = Cx.core state.gcx state.cx in
  let vty = T.Cx.eval tcx ty in
  T.check tcx vty tm;
  ret ()

let fill_hole tm : (dev, dev) move =
  get_hole >>= fun (_, ty) ->
  check ~ty ~tm >>
  set_foc @@ Ret tm

let solve : (cell, cell) move =
  get >>= fun state ->
  match state.cmd.foc with
  | Guess {nm; ty; guess} ->
    let proof = extract guess in
    check ~ty ~tm:proof >>
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

let claim nm ty : (dev, dev) move =
  get >>= fun state ->
  let guess = Guess {nm; ty; guess = Hole ty} in
  set_foc @@ Node (guess, Dev.subst Tm.Proj state.cmd.foc)


let user_hole name : (dev, dev) move =
  get_hole >>= fun (cx, ty) ->
  let lbl_ty = Tm.make @@ Tm.LblTy {lbl = name; args = []; ty} in
  let hole_ty, hole_args = Cx.skolemize cx ~cod:lbl_ty in
  Format.printf "Adding hole of type %a to global context@." (Tm.pp Pretty.Env.emp) hole_ty;
  add_hole name ~ty:hole_ty ~sys:[] >>
  let head = Tm.make @@ Tm.Global name in
  let hole_tm = List.fold_right (fun arg tm -> Tm.make @@ Tm.FunApp (tm, arg)) hole_args head in
  fill_hole @@ Tm.up @@ Tm.make @@ Tm.LblCall hole_tm

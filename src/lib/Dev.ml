type ty = Tm.chk Tm.t
type tm = Tm.chk Tm.t
type boundary = Tm.chk Tm.t Tm.system

type cell =
  | Guess of {nm : string option; ty : ty; guess : dev}
  | Let of {nm : string option; ty : ty; def : tm}
  | Lam of {nm : string option; ty : ty}
  | Specify of boundary (* not sure if this is right *)
  | Restrict of {r : Tm.chk Tm.t; r' : Tm.chk Tm.t}

and dev =
  | Hole
  | B of cell * dev
  | Ret of tm

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


let rec pp_cell env fmt =
  function
  | Guess {nm; ty; guess} ->
    let x, envx = Pretty.Env.bind nm env in
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
    end;
    envx

  | Let {nm; ty; def} ->
    let x, envx = Pretty.Env.bind nm env in
    Format.fprintf fmt "!%a : %a %a %a"
      Uuseg_string.pp_utf_8 x
      (Tm.pp env) ty
      Uuseg_string.pp_utf_8 "▷"
      (Tm.pp env) def;
    envx

  | Lam {nm; ty} ->
    let x, envx = Pretty.Env.bind nm env in
    Format.fprintf fmt "λ%a : %a"
      Uuseg_string.pp_utf_8 x
      (Tm.pp env) ty;
    envx

  | Specify _ ->
    failwith ""

  | Restrict _ ->
    failwith ""

and pp_dev env fmt =
  function
  | Hole ->
    Format.fprintf fmt "?"
  | Ret tm ->
    Format.fprintf fmt "`%a"
      (Tm.pp env) tm
  | B (cell, dev) ->
    let env' = pp_cell env fmt cell in
    Format.fprintf fmt ". %a"
      (pp_dev env') dev

(** Development contexts. Following Conor McBride, we define tactics to be admissible rules
    in the theory of valid contexts. *)
module Cx :
sig
  type t
  val emp : t
  val ext : t -> cell -> t

  val pp_cx : t Pretty.t0

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

  let rec pp_cx_ env fmt =
    function
    | Emp -> env
    | Ext (Emp, c) ->
      pp_cell env fmt c
    | Ext (t, c) ->
      let env' = pp_cx_ env fmt t in
      Format.fprintf fmt "@,";
      pp_cell env' fmt c

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

        | Specify _ ->
          tcx

        | Restrict {r; r'} ->
          let vr = Typing.Cx.eval_dim tcx r in
          let vr' = Typing.Cx.eval_dim tcx r' in
          Typing.Cx.restrict tcx vr vr'
      end
end

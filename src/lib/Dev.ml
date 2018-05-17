type ty = Tm.chk Tm.t
type tm = Tm.chk Tm.t
type boundary = Tm.chk Tm.t Tm.system

type cell =
  | Guess of {ty : ty; guess : dev}
  | Let of {ty : ty; def : tm}
  | Lam of ty
  | Specify of boundary
  | Restrict of {r : Tm.chk Tm.t; r' : Tm.chk Tm.t}

and dev =
  | Hole
  | B of cell * dev
  | Ret of tm

(** Development contexts. Following Conor McBride, we define tactics to be admissible rules
    in the theory of valid contexts. *)
module Cx :
sig
  type t
  val emp : t
  val ext : t -> cell -> t

  val core : t -> Typing.cx
end =
struct
  type t =
    | Emp
    | Ext of t * cell

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
        | Guess {ty; _} ->
          let vty = Typing.Cx.eval tcx ty in
          fst @@ Typing.Cx.ext_ty tcx ~nm:None vty

        | Let {ty; def} ->
          let vty = Typing.Cx.eval tcx ty in
          let vdef = Typing.Cx.eval tcx def in
          Typing.Cx.def tcx ~nm:None ~ty:vty ~el:vdef

        | Lam ty ->
          let vty = Typing.Cx.eval tcx ty in
          fst @@ Typing.Cx.ext_ty tcx ~nm:None vty

        | Specify _ ->
          tcx

        | Restrict {r; r'} ->
          let vr = Typing.Cx.eval_dim tcx r in
          let vr' = Typing.Cx.eval_dim tcx r' in
          Typing.Cx.restrict tcx vr vr'
      end
end

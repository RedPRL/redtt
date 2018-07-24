type cx = LocalCx.t
type value = Val.value
type cofibration = (I.t * I.t) list

type tm = Tm.tm

type _ jdg =
  | Chk : {cx : cx; ty : value; tm : tm} -> unit jdg
  | ChkEval : {cx : cx; ty : value; tm : tm} -> value jdg
  | Eval : tm -> value jdg
  | Ret : 'a -> 'a jdg

type _ kont =
  | KChkFamCod : {cx : cx; univ : value; cod : tm Tm.bnd; kont : unit kont} -> value kont
  | KEval : {cx : cx; tm : Tm.tm; kont : value kont} -> unit kont
  | KDone : unit kont

type state =
  | Cut : 'a jdg * 'a kont -> state


type 'a checkpoint =
  | Result of 'a
  | Error
  | Intermediate : state -> unit checkpoint

let (<:) jdg kont = Intermediate (Cut (jdg, kont))

exception Final

let step : (module LocalCx.S) -> state -> unit checkpoint =
  fun (module Cx) state ->
    let Cut (jdg, kont) = state in
    match jdg with
    | Chk {cx; ty; tm} ->
      begin
        match Cx.Eval.unleash ty, Tm.unleash tm with
        | Val.Univ _, Tm.Pi (dom, cod) ->
          ChkEval {cx; ty; tm = dom}
          <: KChkFamCod {cx; univ = ty; cod; kont}

        | Val.Univ _, Tm.Sg (dom, cod) ->
          ChkEval {cx; ty; tm = dom}
          <: KChkFamCod {cx; univ = ty; cod; kont}

        | Val.Pi {dom; cod}, Tm.Lam (Tm.B (nm, bdy)) ->
          let cxx, x = Cx.ext_ty cx ~nm dom in
          let codx = Cx.Eval.inst_clo cod x in
          Chk {cx = cxx; ty = codx; tm = bdy}
          <: kont

        | _ ->
          failwith ""
      end

    | ChkEval {cx; ty; tm} ->
      Chk {cx; ty; tm} <: KEval {cx; tm; kont}

    | Ret res ->
      begin
        match kont with
        | KEval {cx; tm; kont} ->
          let el = Cx.eval cx tm in
          Ret el <: kont

        | KChkFamCod {cx; univ; cod = Tm.B (nm, bdy); kont} ->
          let dom = res in
          let cxx, _ = Cx.ext_ty cx ~nm dom in
          Chk {cx = cxx; ty = univ; tm = bdy} <: kont

        | KDone ->
          Result ()
      end

    | _ -> failwith ""

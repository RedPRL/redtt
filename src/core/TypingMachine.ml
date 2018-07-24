open RedBasis.Bwd

type cx = LocalCx.t
type value = Val.value
type cofibration = (I.t * I.t) list

type tm = Tm.tm

type constraint_ =
  | ChkEq of {cx : cx; ty : value; el0 : value; el1 : value}

type _ jdg =
  | Chk : {cx : cx; ty : value; tm : tm} -> unit jdg
  | ChkBdry : {cx : cx; ty : value; tm : tm; sys : Val.val_sys} -> unit jdg
  | ChkFace : {cx : cx; ty: value; tm : tm; face : Val.val_face} -> unit jdg
  | ChkEval : {cx : cx; ty : value; tm : tm} -> value jdg
  | Cst : constraint_ -> unit jdg
  | Ret : 'a -> 'a jdg

type _ kont =
  | KChkFamCod : {cx : cx; univ : value; cod : tm Tm.bnd; kont : unit kont} -> value kont
  | KChkPair : {cx : cx; cod : Val.clo; tm : tm; kont : unit kont} -> value kont
  | KEval : {cx : cx; tm : Tm.tm; kont : value kont} -> unit kont
  | KChkBdry : {cx : cx; ty : value; tm : tm; sys : Val.val_sys; kont : unit kont} -> unit kont
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

        | Val.Sg {dom; cod}, Tm.Cons (t0, t1) ->
          ChkEval {cx; ty = dom; tm = t0}
          <: KChkPair {cx; cod; tm = t1; kont}

        | Val.Ext ext, Tm.ExtLam (Tm.NB (nms, bdy)) ->
          let cxx, xs = Cx.ext_dims cx ~nms:(Bwd.to_list nms) in
          let codx, sysx = Cx.Eval.ExtAbs.inst ext @@ Bwd.map (fun x -> `Atom x) @@ Bwd.from_list xs in
          Chk {cx = cxx; ty = codx; tm = bdy} <:
          KChkBdry {cx = cxx; ty = codx; tm = bdy; sys = sysx; kont}

        | _ ->
          failwith ""
      end

    | ChkFace {cx; ty; tm; face} ->
      begin
        match face with
        | Face.True (_, _, el) ->
          Cst (ChkEq {cx; ty; el0 = el; el1 = Cx.eval cx tm}) <: kont
        | Face.False _ ->
          Ret () <: kont
        | Face.Indet (p, el) ->
          let r, r' = Eq.unleash p in
          begin
            try
              let cx', phi = Cx.restrict cx r r' in
              let ty' = Cx.Eval.Val.act phi ty in
              Cst (ChkEq {cx = cx'; ty = ty'; el0 = el; el1 = Cx.eval cx' tm}) <: kont
            with
            | I.Inconsistent ->
              Ret () <: kont
          end
      end

    | ChkBdry {cx; ty; tm; sys} ->
      begin
        match sys with
        | [] ->
          Ret () <: kont

        | face :: sys ->
          ChkFace {cx; ty; tm; face} <:
          KChkBdry {cx; ty; tm; sys; kont}
      end

    | ChkEval {cx; ty; tm} ->
      Chk {cx; ty; tm} <: KEval {cx; tm; kont}

    | Cst (ChkEq {cx; ty; el0; el1}) ->
      begin
        try
          Cx.check_eq cx ~ty el0 el1;
          Ret () <: kont
        with
        | _ -> Error
      end

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

        | KChkPair {cx; cod; tm; kont} ->
          let v = res in
          let codv = Cx.Eval.inst_clo cod v in
          Chk {cx; ty = codv; tm} <: kont

        | KChkBdry {cx; ty; tm; sys; kont} ->
          ChkBdry {cx; ty; tm; sys} <: kont

        | KDone ->
          Result ()
      end

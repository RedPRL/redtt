open RedBasis
open Bwd

type cx = LocalCx.t
type value = Val.value
type cofibration = (I.t * I.t) list

type tm = Tm.tm
type chk = cx * value * tm
type chk_fam = cx * value * value * tm Tm.bnd
type eval = cx * tm

type (_, _) jdg =
  | Eval : (eval, value) jdg
  | Chk : (chk, unit) jdg
  | ChkFam : (chk_fam, unit) jdg

type (_, _) cmd =
  | Jdg : ('rho -> 'rho0) * ('rho0, 'rho1) jdg -> ('rho, 'rho1) cmd

type _ state =
  | Wait : ('rho0, 'rho1) cmd * 'rho1 state -> 'rho0 state
  | Done : 'rho state

type 'a checkpoint =
  | Result of 'a
  | Error
  | Intermediate :
      { env : 'rho;
        kont : 'rho state
      } -> unit checkpoint

let continue k = Intermediate {env = (); kont = k}

let (@>) jdg state =
  Wait (jdg, state)

let rec step : type rho x. (module LocalCx.S) -> rho -> rho state -> unit checkpoint =
  fun (module Cx) env ->
    function
    | Wait (Jdg (chi, jdg), kont) ->
      begin
        match jdg with
        | Eval ->
          let cx, tm = chi env in
          Intermediate {env = Cx.eval cx tm; kont}

        | Chk ->
          let cx, ty, tm = chi env in
          begin
            match Cx.Eval.unleash ty, Tm.unleash tm with
            | Val.Univ _, Tm.Pi (dom, cod) ->
              continue @@
              Jdg ((fun _ -> cx, ty, dom), Chk) @>
              Jdg ((fun _ -> cx, dom), Eval) @>
              Jdg ((fun vdom -> cx, ty, vdom, cod), ChkFam) @>
              kont
            | _ -> failwith ""
          end

        | ChkFam ->
          let cx, univ, dom, fam = chi env in
          let Tm.B (nm, bdy) = fam in
          let cxx, _ = Cx.ext_ty cx ~nm dom in
          continue @@
          Jdg ((fun _ -> cxx, univ, bdy), Chk) @> kont

      end

    | Done ->
      Result ()

let refresh_val : (module LocalCx.S) -> cx -> value -> value -> value =
  fun (module Cx) cx ty el ->
    let tm = Cx.quote cx ~ty el in
    Cx.eval cx tm

let refresh_ty : (module LocalCx.S) -> cx -> value -> value =
  fun ((module Cx) as cxmod) cx ty ->
    let univ = Cx.Eval.make @@ Val.Univ {lvl = Lvl.Omega; kind = Kind.Pre} in
    refresh_val cxmod cx univ ty

let refresh_cx : (module LocalCx.S) -> cx -> cx =
  failwith "TODO"

let refresh_inputs : type rho0 rho1 x. (module LocalCx.S) -> (rho0, rho1) jdg -> rho0 -> rho0 =
  fun ((module Cx) as cxmod) jdg env ->
    match jdg with
    | Chk ->
      let cx, ty, tm = env in
      let cx' = refresh_cx cxmod cx in
      let ty' = refresh_ty cxmod cx' ty in
      cx', ty', tm
    | Eval ->
      let cx, tm = env in
      let cx' = refresh_cx cxmod cx in
      cx', tm
    | ChkFam ->
      let cx, univ, dom, fam = env in
      let cx' = refresh_cx cxmod cx in
      let univ' = refresh_ty cxmod cx' univ in
      let dom' = refresh_ty cxmod cx' dom in
      cx', univ', dom', fam

let rec refresh : type rho x. (module LocalCx.S) -> rho state -> rho state =
  fun cx kont ->
    match kont with
    | Wait (Jdg (chi, jdg), kont) ->
      let chi' x = refresh_inputs cx jdg @@ chi x in
      Wait (Jdg (chi', jdg), kont)
    | Done ->
      Done

let rec driver : type rho x. (module LocalCx.S) -> rho -> rho state -> unit =
  fun cx env kont ->
    match step cx env kont with
    | Error ->
      (* TODO: try to update global environment *)
      let cx' = cx in
      driver cx' env @@ refresh cx' kont

    | Intermediate {env; kont} ->
      driver cx env kont

    | Result () ->
      ()

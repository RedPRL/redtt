open RedBasis open Bwd open BwdNotation
open Combinators

module D = NewDomain
module Q = NewQuote

type positive = [`Type | `El of D.con | `Dim]
type classifier = [`Pos of positive | `Neg of D.con * D.con D.sys]

type error =
  | ExpectedDimension
  | UnexpectedState

exception E of error
exception PleaseRaiseProperError
exception CanJonHelpMe

module type Cx =
sig
  type t
  val rel : t -> NewRestriction.t
  val genv : t -> GlobalEnv.t
  val venv : t -> D.Env.t
  val qenv : t -> Q.QEnv.t

  val extend : t -> ?name:string option -> D.con -> t * D.con
  val extend_dims : t -> ?names:string option list -> t * D.dim list
  val lookup : t -> ?tw:Tm.twin -> int -> classifier
end

module Cx : Cx  =
struct
  type t =
    {rel : NewRestriction.t;
     venv : D.Env.t;
     qenv : Q.QEnv.t;
     hyps : classifier bwd}

  let rel cx = cx.rel
  let genv cx = cx.venv.globals
  let venv cx = cx.venv
  let qenv cx = cx.qenv

  let lookup cx ?(tw = `Only) ix =
    raise CanJonHelpMe

  let extend _ ?name _ =
    raise CanJonHelpMe

  let extend_dims _ ?names =
    raise CanJonHelpMe

end

module TC :
sig
  val check : Cx.t -> classifier -> Tm.tm -> unit
end =
struct

  let eval cx = D.Syn.eval (Cx.rel cx) (Cx.venv cx)
  let inst_clo cx clo v = D.Clo.inst (Cx.rel cx) clo (D.Val (D.LazyVal.make v))


  open Tm.Notation

  module ConsSys = D.Sys (D.Con)


  module Sigma =
  struct
    let split tm =
      match Tm.unleash tm with
      | Tm.Cons (tm0, tm1) ->
        tm0, tm1
      | Tm.Up cmd ->
        Tm.up @@ cmd @< Tm.Fst, Tm.up @@ cmd @< Tm.Snd
      | _ ->
        raise PleaseRaiseProperError


    let split_sys cx sys =
      let sys0 = ConsSys.plug (Cx.rel cx) D.Fst sys in
      let sys1 = ConsSys.plug (Cx.rel cx) D.Snd sys in
      sys0, sys1
  end

  module Pi =
  struct
    let body tm =
      match Tm.unleash tm with
      | Tm.Lam (Tm.B (_, bdy)) ->
        bdy
      | Tm.Up cmd ->
        let wk = Tm.shift 1 in
        let cmd' = Tm.subst_cmd wk cmd in
        let var = Tm.up @@ Tm.ix 0 in
        let frm = Tm.FunApp var in
        Tm.up @@ cmd' @< frm
      | _ ->
        raise PleaseRaiseProperError

    let sys_body cx x sys =
      ConsSys.plug (Cx.rel cx) (D.FunApp (D.TypedVal.make (D.Val.make x))) sys

  end

  module Ext =
  struct
    let body cx xs tm =
      match Tm.unleash tm with
      | Tm.ExtLam (Tm.NB (_, bdy)) ->
        bdy
      | Tm.Up cmd ->
        let n = List.length xs in
        let wk = Tm.shift n in
        let trs =
          flip List.map xs @@ fun x ->
          Q.Q.equate_dim (Cx.qenv cx) (Cx.rel cx) x x
        in
        let cmd' = Tm.subst_cmd wk cmd in
        let frm = Tm.ExtApp trs in
        Tm.up @@ cmd' @< frm
      | _ ->
        raise PleaseRaiseProperError

    let sys_body cx xs sys =
      ConsSys.plug (Cx.rel cx) (D.ExtApp xs) sys
  end

  let rec check cx (cls : classifier) tm =
    match cls, Tm.unleash tm with
    | `Pos `Dim, (Tm.Dim0 | Tm.Dim1) ->
      ()

    | `Pos pos, Tm.Up cmd ->
      let pos' = synth cx cmd in
      approx cx pos' pos


    | `Neg (D.Sg q, sys), _ ->
      let tm0, tm1 = Sigma.split tm in
      let sys0, sys1 = Sigma.split_sys cx sys in
      let dom = D.Val.unleash q.dom in
      check_of_ty cx dom sys0 tm0;
      let el0 = eval cx tm0 in
      let cod = inst_clo cx q.cod el0 in
      check_of_ty cx cod sys1 tm1

    | `Neg (D.Pi q, sys), _ ->
      let cx', x = Cx.extend cx @@ D.Val.unleash q.dom in
      let bdy = Pi.body tm in
      let bdy_sys = Pi.sys_body cx x sys in
      let cod = inst_clo cx q.cod x in
      check_of_ty cx cod bdy_sys bdy

    | `Neg (D.Ext eclo, sys), _ ->
      let names = Bwd.to_list @@ D.ExtClo.names eclo in
      let cx', xs = Cx.extend_dims cx ~names in
      let bdy = Ext.body cx xs tm in
      let bdy_sys = Ext.sys_body cx xs sys in
      let cod, cod_sys = D.ExtClo.inst (Cx.rel cx) eclo @@ List.map (fun x -> D.Dim x) xs in
      check_of_ty cx cod (cod_sys @ bdy_sys) bdy

    | _ ->
      raise @@ E UnexpectedState

  and check_of_ty cx ty sys tm =
    match ty with
    | D.Pi _ | D.Sg _ | D.Ext _ ->
      check cx (`Neg (ty, sys)) tm
    | D.Univ _ | D.Data _ | D.Neu _ ->
      check cx (`Pos (`El ty)) tm;
      check_boundary cx ty sys @@
      eval cx tm
    | _ ->
      raise CanJonHelpMe

  and check_boundary cx ty sys el =
    raise CanJonHelpMe

  and synth cx cmd : positive =
    raise CanJonHelpMe

  and approx cx (pos0 : positive) (pos1 : positive) =
    raise CanJonHelpMe

end

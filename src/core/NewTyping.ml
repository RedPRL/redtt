open RedBasis open Bwd
open Combinators

module D = NewDomain
module Q = NewQuote
type error =
  | ExpectedDimension
  | UnexpectedState
  | PolarityMismatch
  | UniverseError
  | ExpectedType

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
  val lookup : t -> ?tw:Tm.twin -> int -> D.con
end

module Cx : Cx  =
struct
  type t =
    {rel : NewRestriction.t;
     venv : D.Env.t;
     qenv : Q.QEnv.t;
     hyps : [`Dim | `Ty of D.con] bwd}

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
  val check_ty : Cx.t -> Kind.t -> Tm.tm -> Lvl.t
  val check_of_ty : Cx.t -> D.con -> D.con D.sys -> Tm.tm -> unit
end =
struct

  type positive = [`El of D.con | `Dim]
  type phase = [`Pos of positive | `Neg of D.con * D.con D.sys]


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
          Q.equate_dim (Cx.qenv cx) (Cx.rel cx) x x
        in
        let cmd' = Tm.subst_cmd wk cmd in
        let frm = Tm.ExtApp trs in
        Tm.up @@ cmd' @< frm
      | _ ->
        raise PleaseRaiseProperError

    let sys_body cx xs sys =
      ConsSys.plug (Cx.rel cx) (D.ExtApp xs) sys
  end


  let polarity =
    function
    | D.Pi _ | D.Sg _ | D.Ext _ ->
      `Neg
    | D.Univ _ | D.Data _ | D.Neu _ ->
      `Pos
    | _ ->
      raise CanJonHelpMe



  let rec check cx (phase : phase) tm =
    match phase, Tm.unleash tm with
    | `Pos pos, Tm.Up cmd ->
      let pos' = synth cx cmd in
      approx_pos cx pos' pos

    | `Pos `Dim, (Tm.Dim0 | Tm.Dim1) ->
      ()

    | `Pos (`El (D.Univ univ)), _->
      let lvl = check_ty cx univ.kind tm in
      if Lvl.greater lvl univ.lvl then
        raise @@ E UniverseError

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

  (* TODO: we can take from RedPRL the fine-grained subtraction of kinds. Let Favonia do it! *)
  and check_ty cx kind tm : Lvl.t =
    match Tm.unleash tm with
    | Tm.Up cmd ->
      begin
        match synth cx cmd with
        | `El (D.Univ univ) when Kind.lte univ.kind kind ->
          univ.lvl
        | `El (D.Univ univ) ->
          raise @@ E UniverseError
        | _ ->
          raise @@ E ExpectedType
      end

    | Tm.Univ univ ->
      Lvl.shift 1 univ.lvl

    | Tm.Pi (dom, Tm.B (name, cod)) | Tm.Sg (dom, Tm.B (name, cod)) ->
      let lvl0 = check_ty cx kind dom in
      let vdom = eval cx dom in
      let cx', _ = Cx.extend cx ~name vdom in
      check_ty cx' kind cod

    | _ ->
      raise CanJonHelpMe


  and check_of_ty cx ty sys tm =
    match polarity ty with
    | `Pos ->
      check cx (`Pos (`El ty)) tm;
      check_boundary cx ty sys @@
      eval cx tm
    | `Neg ->
      check cx (`Neg (ty, sys)) tm

  and check_boundary cx ty sys el =
    raise CanJonHelpMe

  and synth cx cmd : positive =
    raise CanJonHelpMe

  and approx cx ty0 ty1 =
    match polarity ty0, polarity ty1 with
    | `Pos, `Pos ->
      approx_pos cx (`El ty0) (`El ty1)
    | `Neg, `Neg ->
      let cx', _ = Cx.extend cx ty0 in
      let tm = Tm.up @@ Tm.ix 0 in
      check cx (`Neg (ty1, [])) tm
    | _ ->
      raise @@ E PolarityMismatch

  and approx_pos cx (pos0 : positive) (pos1 : positive) =
    match pos0, pos1 with
    | `Dim, `Dim -> ()
    | _ ->
      raise CanJonHelpMe

end

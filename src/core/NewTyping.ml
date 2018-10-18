open RedBasis open Bwd

module D = NewDomain
module Q = NewQuote

type positive = [`Type | `El of D.con | `Dim]
type classifier = [`Pos of positive | `Neg of D.con]

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
  let genv cx = D.Env.(cx.venv.globals)
  let venv cx = cx.venv
  let qenv cx = cx.qenv

  let lookup cx ?(tw = `Only) ix =
    raise CanJonHelpMe

end

module TC :
sig
  val check : Cx.t -> classifier -> Tm.tm -> unit
end =
struct

  let dispatch ty =
    match ty with
    | D.Pi _ | D.Sg _ ->
      `Neg ty
    | D.Univ _ | D.Data _ | D.Neu _ ->
      `Pos (`El ty)
    | _ ->
      raise CanJonHelpMe

  let eval cx = D.Syn.eval (Cx.rel cx) (Cx.venv cx)
  let inst_clo cx = D.Clo.inst (Cx.rel cx)


  open Tm.Notation

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
  end

  let rec check cx (cls : classifier) tm =
    match cls, Tm.unleash tm with
    | `Pos `Dim, (Tm.Dim0 | Tm.Dim1) ->
      ()

    | `Pos pos, Tm.Up cmd ->
      let pos' = synth cx cmd in
      approx cx pos' pos


    | `Neg (D.Sg q), _ ->
      let tm0, tm1 = Sigma.split tm in
      let dom = D.Val.unleash q.dom in
      check_of_ty cx dom tm0;
      let el0 = eval cx tm0 in
      let cod = inst_clo cx q.cod @@ D.Val (D.LazyVal.make el0) in
      check_of_ty cx cod tm1

    | `Neg (D.Pi q), _ ->
      let cx', x = raise CanJonHelpMe in
      let bdy = Pi.body tm in
      let cod = inst_clo cx q.cod @@ D.Val (D.LazyVal.make x) in
      check_of_ty cx cod bdy

    | _ ->
      raise @@ E UnexpectedState

  and check_of_ty cx ty =
    check cx @@ dispatch ty

  and synth cx cmd : positive =
    raise CanJonHelpMe

  and approx cx (pos0 : positive) (pos1 : positive) =
    raise CanJonHelpMe

end

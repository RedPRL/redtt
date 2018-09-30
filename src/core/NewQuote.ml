open RedBasis
open Bwd
open NewDomain
module Rel = NewRestriction

exception PleaseFillIn
exception PleaseRaiseProperError
exception CanJonHelpMe
exception CanFavoniaHelpMe

module QEnv :
sig
  type t

  val emp : unit -> t (* maybe just [emp : t]? *)

  (** [extend] gives you a new variable (in its level)
      and the new environment extended with that variable. *)
  val extend : t -> int * t

  val abs : Name.t bwd -> t -> t
  val abs1 : Name.t -> t -> t

  val ix_of_lvl : int -> t -> int
  val ix_of_atom : Name.t -> t -> int (* might throw Not_found *)
end =
struct
  module M = Map.Make (Name)
  type t = {n_minus_one : int; atoms : int M.t}

  let emp () = {n_minus_one = -1; atoms = M.empty}

  let extend qenv =
    let n = qenv.n_minus_one + 1 in
    n, {qenv with n_minus_one = n}

  let abs1 x qenv =
    let lvl, qenv = extend qenv in
    {qenv with atoms = M.add x lvl qenv.atoms}

  let abs xs qenv =
    Bwd.fold_left (fun qenv x -> abs1 x qenv) qenv xs

  let ix_of_lvl l qenv =
    qenv.n_minus_one - l

  let ix_of_atom x qenv =
    let lvl = M.find x qenv.atoms in
    ix_of_lvl lvl qenv
end

type qenv = QEnv.t

module Q :
sig
  val equate_dim : qenv -> rel -> I.t -> I.t -> Tm.tm
  (* favonia: whether these should take a value or con as arguments will hopefully be clear in the future. *)
  val equate_nf : qenv -> rel -> con -> con -> con -> Tm.tm
  val equate_neu : qenv -> rel -> neu -> neu -> Tm.tm Tm.cmd
  val equate_ty : qenv -> rel -> con -> con -> Tm.tm
  val equate_nf_sys : qenv -> rel -> con -> con sys -> con sys -> (Tm.tm, Tm.tm) Tm.system

  val subtype : qenv -> rel -> con -> con -> unit
end =
struct
  let ignore _ = ()

  let extend_with_sys qenv ty sys =
    let lvl, qenv = QEnv.extend qenv in
    let neu = {head = Lvl lvl; frames = Emp} in
    Neu {ty; neu; sys}, qenv

  let extend qenv ty = extend_with_sys qenv ty []

  let quote_dim qenv =
    function
    | `Dim0 -> Tm.make Tm.Dim0
    | `Dim1 -> Tm.make Tm.Dim1
    | `Atom x ->
      match QEnv.ix_of_atom x qenv with
      | ix -> Tm.up @@ Tm.ix ix
      | exception Not_found -> Tm.up @@ Tm.var x

  let equate_dim qenv rel r0 r1 =
    match Rel.compare r0 r1 rel with
    | `Same -> quote_dim qenv r0
    | _ -> raise PleaseRaiseProperError

  let rec equate_nf qenv rel ty el0 el1 =
    match ty with
    | Pi {dom; cod} ->
      let x, qenv_x = extend qenv dom in
      let bdy_x =
        let cod_x = Clo.inst rel cod (Val (LazyVal.make @@ lazy x)) in
        let bdy0_x = Con.plug rel (FunApp (Val.make x)) el0 in
        let bdy1_x = Con.plug rel (FunApp (Val.make x)) el1 in
        equate_nf qenv_x rel cod_x bdy0_x bdy1_x
      in
      (* TODO preserve names during evaluation *)
      Tm.lam None bdy_x

    | Univ _ -> equate_ty qenv rel el0 el1

    | _ -> raise PleaseFillIn

  and equate_neu _ = raise PleaseFillIn

  and equate_ty qenv rel ty0 ty1 =
    match ty0, ty1 with
    | Pi info0, Pi info1 ->
      let dom =
        let dom0 = Val.unleash info0.dom in
        let dom1 = Val.unleash info1.dom in
        equate_ty qenv rel dom0 dom1
      in
      let x, qenv_x = extend qenv info0.dom in
      let cod_x =
        let cod0_x = Clo.inst rel info0.cod (Val (LazyVal.make @@ lazy x)) in
        let cod1_x = Clo.inst rel info1.cod (Val (LazyVal.make @@ lazy x)) in
        equate_ty qenv_x rel cod0_x cod1_x
      in
      (* TODO preserve names during evaluation *)
      Tm.pi None dom cod_x

    | _ -> raise PleaseFillIn

  and equate_nf_sys _ = raise PleaseFillIn

  and subtype qenv rel ty0 ty1 =
    ignore @@ equate_ty qenv rel ty0 ty1;
    raise CanJonHelpMe
end

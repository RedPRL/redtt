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
    match el0, el1 with
    | Neu neu0, Neu neu1 ->
      Tm.up @@ equate_neu qenv rel neu0.neu neu1.neu
    | _ ->
      match ty with
      | Pi {dom; cod} ->
        let x, qenv_x = extend qenv dom in
        let cod_x = Clo.inst rel cod (Val (LazyVal.make @@ lazy x)) in
        let bdy0_x = Con.plug rel (FunApp (Val.make x)) el0 in
        let bdy1_x = Con.plug rel (FunApp (Val.make x)) el1 in
        let bdy_x = equate_nf qenv_x rel cod_x bdy0_x bdy1_x in
        Tm.lam (Clo.name cod) bdy_x

      | Sg {dom; cod} ->
        let fst0 = Con.plug rel Fst el0 in
        let fst1 = Con.plug rel Fst el1 in
        let fst = equate_nf qenv rel (Val.unleash dom) fst0 fst1 in
        let cod = Clo.inst rel cod (Val (LazyVal.make @@ lazy fst0)) in
        let snd0 = Con.plug rel Snd el0 in
        let snd1 = Con.plug rel Snd el1 in
        let snd = equate_nf qenv rel cod snd0 snd1 in
        Tm.cons fst snd

      | Ext extclo ->
        let nms = ExtClo.names extclo in
        let xs = Bwd.map Name.named nms in
        let qenv_xs = QEnv.abs xs qenv in
        let rs = Bwd.fold_right (fun x rs -> `Atom x :: rs) xs [] in
        let ty_xs = ExtClo.inst_then_fst rel extclo (List.map (fun r -> Dim r) rs) in
        let bdy0_xs = Con.plug rel (ExtApp rs) el0 in
        let bdy1_xs = Con.plug rel (ExtApp rs) el1 in
        let bdy_xs = equate_nf qenv_xs rel ty_xs bdy0_xs bdy1_xs in
        Tm.ext_lam nms bdy_xs

      | HCom ({ty = `Pos; _} as hcom) ->
        raise PleaseFillIn

      | Univ _ -> equate_ty qenv rel el0 el1

      | _ -> raise PleaseFillIn

  and equate_neu _ = raise PleaseFillIn

  and equate_ty_clo qenv rel dom clo0 clo1 =
    let x, qenv_x = extend qenv dom in
    let lazyx = LazyVal.make @@ lazy x in
    let clo0_x = Clo.inst rel clo0 (Val lazyx) in
    let clo1_x = Clo.inst rel clo1 (Val lazyx) in
    equate_ty qenv_x rel clo0_x clo1_x

  and equate_ty_quantifier qenv rel quant0 quant1 =
    let dom = equate_ty qenv rel (Val.unleash quant0.dom) (Val.unleash quant1.dom) in
    let cod = equate_ty_clo qenv rel quant0.dom quant0.cod quant1.cod in
    dom, (Clo.name quant0.cod, cod)

  and equate_ty qenv rel ty0 ty1 =
    match ty0, ty1 with
    | Neu neu0, Neu neu1 ->
      Tm.up @@ equate_neu qenv rel neu0.neu neu1.neu

    | Pi pi0, Pi pi1 ->
      let dom, (nm, cod) = equate_ty_quantifier qenv rel pi0 pi1 in
      Tm.pi nm dom cod

    | Sg sg0, Sg sg1 ->
      let dom, (nm, cod) = equate_ty_quantifier qenv rel sg0 sg1 in
      Tm.sg nm dom cod

    | Ext extclo0, Ext extclo1 ->
      let nms = ExtClo.names extclo0 in
      let xs = Bwd.map Name.named nms in
      let qenv_xs = QEnv.abs xs qenv in
      let cells = Bwd.fold_right (fun x rs -> Dim (`Atom x) :: rs) xs [] in
      let ty0_xs, sys0_xs = ExtClo.inst rel extclo0 cells in
      let ty1_xs, sys1_xs = ExtClo.inst rel extclo1 cells in
      let ty_xs = equate_ty qenv_xs rel ty0_xs ty1_xs in
      let sys_xs = equate_nf_sys qenv_xs rel ty0_xs sys0_xs sys1_xs in
      Tm.make @@ Tm.Ext (Tm.NB (nms, (ty_xs, sys_xs)))

    | HCom ({ty = `Pos; _} as hcom0), HCom ({ty = `Pos; _} as hcom1) ->
      let r = equate_dim qenv rel hcom0.r hcom1.r in
      let r' = equate_dim qenv rel hcom0.r' hcom1.r' in
      let cap = equate_ty qenv rel (Val.unleash hcom0.cap) (Val.unleash hcom1.cap) in
      let sys = equate_ty_abs_sys qenv rel hcom0.sys hcom1.sys in
      Tm.make @@ Tm.FHCom {r; r'; cap; sys}

    | Univ univ0, Univ univ1 ->
      if univ0.kind = univ1.kind && univ0.lvl = univ1.lvl then
        Tm.univ ~kind:univ0.kind ~lvl:univ0.lvl
      else
        raise PleaseRaiseProperError

    | _ -> raise PleaseFillIn

  and equate_abs qenv rel ty abs0 abs1 =
    let nm = let Abs (x, _) = abs0 in Name.name x in
    let x = Name.named nm in
    let qenv_x = QEnv.abs1 x qenv in
    let bdy0_x = ConAbs.inst rel abs0 (`Atom x) in
    let bdy1_x = ConAbs.inst rel abs1 (`Atom x) in
    let bdy_x = equate_nf qenv_x rel ty bdy0_x bdy1_x in
    Tm.B (nm, bdy_x)

  and equate_ty_abs qenv rel abs0 abs1 =
    let nm = let Abs (x, _) = abs0 in Name.name x in
    let x = Name.named nm in
    let qenv_x = QEnv.abs1 x qenv in
    let bdy0_x = ConAbs.inst rel abs0 (`Atom x) in
    let bdy1_x = ConAbs.inst rel abs1 (`Atom x) in
    let bdy_x = equate_ty qenv_x rel bdy0_x bdy1_x in
    Tm.B (nm, bdy_x)

  and equate_ty_abs_face qenv rel (r0, r'0, abs0) (r1, r'1, abs1) =
    let r = equate_dim qenv rel r0 r1 in
    let r' = equate_dim qenv rel r'0 r'1 in
    let rel = Rel.equate' r0 r'0 rel in
    let lazy abs0 = LazyValAbs.unleash abs0 in
    let lazy abs1 = LazyValAbs.unleash abs1 in
    r, r', Some (equate_ty_abs qenv rel abs0 abs1)

  and equate_abs_face qenv rel ty (r0, r'0, abs0) (r1, r'1, abs1) =
    let r = equate_dim qenv rel r0 r1 in
    let r' = equate_dim qenv rel r'0 r'1 in
    let rel = Rel.equate' r0 r'0 rel in
    let lazy abs0 = LazyValAbs.unleash abs0 in
    let lazy abs1 = LazyValAbs.unleash abs1 in
    r, r', Some (equate_abs qenv rel ty abs0 abs1)

  and equate_nf_face qenv rel ty (r0, r'0, bdy0) (r1, r'1, bdy1) =
    let r = equate_dim qenv rel r0 r1 in
    let r' = equate_dim qenv rel r'0 r'1 in
    let rel = Rel.equate' r0 r'0 rel in
    let lazy bdy0 = LazyVal.unleash bdy0 in
    let lazy bdy1 = LazyVal.unleash bdy1 in
    r, r', Some (equate_nf qenv rel ty bdy0 bdy1)

  and equate_sys_wrapper : 'a 'b. ('a -> 'a -> 'b) -> 'a list -> 'a list -> 'b list =
    fun face_equater sys0 sys1 ->
    try
      List.map2 face_equater sys0 sys1
    with
    | Invalid_argument _ ->
      raise PleaseRaiseProperError (* mismatched lengths *)

  and equate_abs_sys qenv rel ty = equate_sys_wrapper (equate_abs_face qenv rel ty)
  and equate_ty_abs_sys qenv rel = equate_sys_wrapper (equate_ty_abs_face qenv rel)
  and equate_nf_sys qenv rel ty = equate_sys_wrapper (equate_nf_face qenv rel ty)

  and subtype qenv rel ty0 ty1 =
    ignore @@ equate_ty qenv rel ty0 ty1;
    raise CanJonHelpMe
end

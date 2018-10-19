open RedBasis
open Bwd open BwdNotation
open NewDomain
module Rel = NewRestriction

exception PleaseFillIn
exception PleaseRaiseProperError
exception CanJonHelpMe
(* exception CanFavoniaHelpMe *)

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

let ignore _ = ()

let extend_with_sys qenv ty sys =
  let lvl, qenv = QEnv.extend qenv in
  let neu = {neu = DelayedNeu.make {head = Lvl lvl; frames = Emp}; sys} in
  Neu {ty; neu}, qenv

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

let rec equate_con qenv rel ty el0 el1 =
  match el0, el1 with
  | Neu neu0, Neu neu1 ->
    equate_neutroid qenv rel neu0.neu neu1.neu
  | _ ->
    match ty with
    | Pi {dom; cod}  ->
      let x, qenv_x = extend qenv dom in
      let cod_x = Clo.inst rel cod (Val (LazyVal.make x)) in
      let bdy0_x = Con.run rel @@ Con.plug rel (FunApp (TypedVal.make @@ Val.make x)) el0 in
      let bdy1_x = Con.run rel @@ Con.plug rel (FunApp (TypedVal.make @@ Val.make x)) el1 in
      let bdy_x = equate_con qenv_x rel cod_x bdy0_x bdy1_x in
      Tm.lam (Clo.name cod) bdy_x

    | Sg {dom; cod} ->
      let fst0 = Con.run rel @@ Con.plug rel Fst el0 in
      let fst1 = Con.run rel @@ Con.plug rel Fst el1 in
      let fst = equate_con qenv rel (Val.unleash dom) fst0 fst1 in
      let cod = Clo.inst rel cod (Val (LazyVal.make fst0)) in
      let snd0 = Con.run rel @@ Con.plug rel Snd el0 in
      let snd1 = Con.run rel @@ Con.plug rel Snd el1 in
      let snd = equate_con qenv rel cod snd0 snd1 in
      Tm.cons fst snd

    | Ext extclo ->
      let nms = ExtClo.names extclo in
      let xs = Bwd.map Name.named nms in
      let qenv_xs = QEnv.abs xs qenv in
      let rs = Bwd.fold_right (fun x rs -> `Atom x :: rs) xs [] in
      let ty_xs = ExtClo.inst_then_fst rel extclo (List.map (fun r -> Dim r) rs) in
      let bdy0_xs = Con.run rel @@ Con.plug rel (ExtApp rs) el0 in
      let bdy1_xs = Con.run rel @@ Con.plug rel (ExtApp rs) el1 in
      let bdy_xs = equate_con qenv_xs rel ty_xs bdy0_xs bdy1_xs in
      Tm.ext_lam nms bdy_xs

    | Restrict face ->
      let r, r', ty_rr' = face in
      let tr = quote_dim qenv r in
      let tr' = quote_dim qenv r' in
      let rel_rr' = Rel.equate' r r' rel in
      let force0 = Con.run rel_rr' @@ Con.plug rel_rr' RestrictForce el0 in
      let force1 = Con.run rel_rr' @@ Con.plug rel_rr' RestrictForce el1 in
      let bdy = equate_con qenv rel_rr' (LazyVal.unleash ty_rr') force0 force1 in
      Tm.make @@ Tm.RestrictThunk (tr, tr', Some bdy)

    | V {r; ty0; ty1; equiv} ->
      let tr = quote_dim qenv r in
      let rel_r0 = Rel.equate' r `Dim0 rel in
      let tm0 = equate_con qenv rel_r0 (Val.unleash ty0) (Con.run rel_r0 el0) (Con.run rel_r0 el1) in
      let func = Val.run rel_r0 @@ Val.plug rel_r0 Fst equiv in
      let vproj0 = Con.run rel @@ Con.plug rel (VProj {r; func = TypedVal.make func}) el0 in
      let vproj1 = Con.run rel @@ Con.plug rel (VProj {r; func = TypedVal.make func}) el1 in
      let tm1 = equate_con qenv rel (Val.unleash ty1) vproj0 vproj1 in
      Tm.make @@ Tm.VIn {r = tr; tm0; tm1}

    | HCom ({r; r'; ty = `Pos; cap = ty; sys} as hcom) ->
      let tr, tr' = quote_dim qenv r, quote_dim qenv r' in
      let cap0 = Con.run rel @@ Con.plug rel (Cap {r; r'; ty; sys}) el0 in
      let cap1 = Con.run rel @@ Con.plug rel (Cap {r; r'; ty; sys}) el1 in
      let tcap = equate_con qenv rel (Val.unleash ty) cap0 cap1 in
      let equate_boundary (ri, r'i, abs) =
        let rel = Rel.equate' ri r'i rel in
        let tri, tr'i = quote_dim qenv ri, quote_dim qenv r'i in
        let b = equate_con qenv rel (ConAbs.inst rel (LazyValAbs.unleash abs) r') (Con.run rel el0) (Con.run rel el1) in
        tri, tr'i, Some b
      in
      let tsys = List.map equate_boundary sys in
      Tm.make @@ Tm.Box {r = tr; r' = tr'; cap = tcap; sys = tsys}

    | Data data ->
      begin
        match el0, el1 with
        | Intro intro0, Intro intro1 when intro0.clbl = intro1.clbl ->

          let rec go acc tyenv tele args0 args1 =
            match tele, args0, args1 with
            | Desc.TNil _, [], [] ->
              Bwd.to_list acc

            | Desc.TCons (`Const ty, Tm.B (_, tele)), `Const v0 :: args0, `Const v1 :: args1 ->
              let vty = Syn.eval rel tyenv ty in
              let tm = equate_val qenv rel vty v0 v1 in
              let tyenv = Env.extend_cell tyenv @@ Val (LazyVal.make_from_delayed v0) in
              go (acc #< tm) tyenv tele args0 args1

            | Desc.TCons (`Rec Desc.Self, Tm.B (_, tele)), `Rec (_, v0) :: args0, `Rec (_, v1) :: args1 ->
              let vty = Data data in
              let tm = equate_val qenv rel vty v0 v1 in
              let tyenv = Env.extend_cell tyenv @@ Val (LazyVal.make_from_delayed v0) in
              go (acc #< tm) tyenv tele args0 args1

            | Desc.TCons (`Dim, Tm.B (_, tele)), `Dim r0 :: args0, `Dim r1 :: args1 ->
              let tr = equate_dim qenv rel r0 r1 in
              let tyenv = Env.extend_cell tyenv @@ Dim r0 in
              go (acc #< tr) tyenv tele args0 args1

            | _ ->
              (* unequal length *)
              raise PleaseRaiseProperError
          in

          let clbl = intro0.clbl in
          let genv, constrs = data.constrs in
          let constr = Desc.lookup_constr clbl constrs in
          let tyenv0 = Env.init genv in
          let tyenv = Env.extend_cells tyenv0 data.params in
          let args = go Emp tyenv constr intro0.args intro1.args in
          let params =
            let desc = GlobalEnv.lookup_datatype data.lbl genv in
            equate_data_params qenv rel tyenv0 desc.body data.params data.params
          in

          Tm.make @@ Tm.Intro (data.lbl, clbl, failwith "params", args)

        | HCom ({ty = `Pos; _} as hcom0), HCom ({ty = `Pos; _} as hcom1) ->
          let r = equate_dim qenv rel hcom0.r hcom1.r in
          let r' = equate_dim qenv rel hcom0.r' hcom1.r' in
          let cap = equate_con qenv rel ty (Val.unleash hcom0.cap) (Val.unleash hcom1.cap) in
          let sys = equate_con_abs_sys qenv rel ty hcom0.sys hcom1.sys in
          Tm.make @@ Tm.FHCom {r; r'; cap; sys}

        | _ ->
          raise PleaseRaiseProperError
      end

    | Univ _ ->
      equate_tycon qenv rel el0 el1

    | _ ->
      (* This might be done? *)
      raise PleaseFillIn

and equate_data_params qenv rel tyenv tele params0 params1 =
  let rec go acc tyenv tele prms0 prms1 =
    match tele, prms0, prms1 with
    | Desc.TNil _, [], [] ->
      Bwd.to_list acc

    | Desc.TCons (ty, Tm.B (_, tele)), Val v0 :: prms0, Val v1 :: prms1 ->
      let vty = Syn.eval rel tyenv ty in
      let tm = equate_con qenv rel vty (LazyVal.unleash v0) (LazyVal.unleash v1) in
      let tyenv = Env.extend_cell tyenv @@ Val v0 in
      go (acc #< tm) tyenv tele prms0 prms1

    | _ ->
      raise PleaseRaiseProperError
  in
  go Emp tyenv tele params0 params1

and equate_in_neutral_ty qenv rel el0 el1 =
  match el0, el1 with
  | Neu neu0, Neu neu1 ->
    equate_neutroid qenv rel neu0.neu neu1.neu
  | _ ->
    raise PleaseRaiseProperError

and equate_val qenv rel ty val0 val1 =
  equate_con qenv rel ty (Val.unleash val0) (Val.unleash val1)

and equate_neu qenv rel neu0 neu1 =
  let hd = equate_hd qenv rel neu0.head neu1.head in
  let stk = Bwd.fold_right2
      (fun f0 f1 stk -> equate_frame qenv rel f0 f1 :: stk)
      neu0.frames neu1.frames []
  in
  Tm.make @@ Tm.Up (hd, stk)

and equate_neutroid qenv rel neu0 neu1 =
  equate_neu qenv rel (DelayedNeu.unleash neu0.neu) (DelayedNeu.unleash neu1.neu)

and equate_neutroid_abs qenv rel abs0 abs1 =
  let nm = let Abs (x, _) = abs0 in Name.name x in
  let x = Name.named nm in
  let qenv_x = QEnv.abs1 x qenv in
  let bdy0_x = NeutroidAbs.inst rel abs0 (`Atom x) in
  let bdy1_x = NeutroidAbs.inst rel abs1 (`Atom x) in
  let bdy_x = equate_neutroid qenv_x rel bdy0_x bdy1_x in
  Tm.B (nm, bdy_x)

and equate_hd qenv rel hd0 hd1 =
  match hd0, hd1 with
  | Lvl l0, Lvl l1 ->
    if l0 = l1 then
      Tm.Ix (QEnv.ix_of_lvl l0 qenv, `Only)
    else
      raise PleaseRaiseProperError
  | Var info0, Var info1 ->
    if info0.name = info1.name && info0.twin = info1.twin && info0.ushift = info1.ushift then
      Tm.Var {name = info0.name; twin = info0.twin; ushift = info0.ushift}
    else
      raise PleaseRaiseProperError
  | Meta info0, Meta info1 ->
    if info0.name = info1.name && info0.ushift = info1.ushift then
      Tm.Meta {name = info0.name; ushift = info0.ushift}
    else
      raise PleaseRaiseProperError

  | NCoe info0, NCoe info1 ->
    let r = equate_dim qenv rel info0.r info1.r in
    let r' = equate_dim qenv rel info0.r' info1.r' in
    let ty = equate_neutroid_abs qenv rel info0.ty info1.ty in
    let tm =
      let univ = Val.make @@ Univ {kind = `Pre; lvl = `Omega} in
      let neu = NeutroidAbs.inst rel info0.ty info0.r in
      let ty_r = Con.run rel @@ Neu {ty = univ; neu} in
      equate_con qenv rel ty_r (Val.unleash info0.cap) (Val.unleash info1.cap)
    in
    Tm.Coe {r; r'; ty; tm}

  | NHCom info0, NHCom info1 ->
    let r = equate_dim qenv rel info0.r info1.r in
    let r' = equate_dim qenv rel info0.r' info1.r' in
    let ty = equate_neutroid qenv rel info0.ty info1.ty in
    let ty_val =
      let univ = Val.make @@ Univ {kind = `Pre; lvl = `Omega} in
      Con.run rel @@ Neu {ty = univ; neu = info0.ty}
    in
    let cap = equate_val qenv rel ty_val info0.cap info1.cap in
    let sys = equate_con_abs_sys qenv rel ty_val info0.sys info1.sys in
    Tm.HCom {r; r'; ty; cap; sys}

  | _ -> raise PleaseRaiseProperError

and equate_frame qenv rel frm0 frm1 =
  match frm0, frm1 with
  | FunApp {ty = Some ty0; value = v0}, FunApp {ty = Some ty1; value = v1} ->
    let _ = equate_tyval qenv rel ty0 ty1 in
    let tm = equate_val qenv rel (Val.unleash ty0) v0 v1 in
    Tm.FunApp tm

  | Fst, Fst ->
    Tm.Fst

  | Snd, Snd ->
    Tm.Snd

  | ExtApp rs0, ExtApp rs1 ->
    let rs = List.map2 (equate_dim qenv rel) rs0 rs1 in
    Tm.ExtApp rs

  | RestrictForce, RestrictForce ->
    Tm.RestrictForce

  | VProj {r = r0; func = {ty = Some func_ty0; value = func0}},
    VProj {r = r1; func = {ty = Some func_ty1; value = func1}} ->
    let r = equate_dim qenv rel r0 r1 in
    let func_ty0 = Val.unleash func_ty0 in
    let func_ty1 = Val.unleash func_ty1 in
    begin
      match func_ty0, func_ty1 with
      | Pi qu0, Pi qu1 ->
        let ty0 = equate_tyval qenv rel qu0.dom qu1.dom in
        let dummy = LazyVal.make FortyTwo in
        let cod0 = Val.make @@ Clo.inst rel qu0.cod @@ Val dummy in
        let cod1 = Val.make @@ Clo.inst rel qu1.cod @@ Val dummy in
        let ty1 = equate_tyval qenv rel cod0 cod1 in
        let func = equate_val qenv rel func_ty0 func0 func1 in
        Tm.VProj {r; ty0; ty1; func}
      | _ ->
        raise PleaseRaiseProperError
    end

  | Cap info0, Cap info1 ->
    let r = equate_dim qenv rel info0.r info1.r in
    let r' = equate_dim qenv rel info0.r' info1.r' in
    let ty = equate_tyval qenv rel info0.ty info1.ty in
    let sys = equate_tycon_abs_sys qenv rel info0.sys info1.sys in
    Tm.Cap {r; r'; ty; sys}

  | Elim elim0, Elim elim1 ->
    raise CanJonHelpMe

  | _ ->
    raise PleaseRaiseProperError

and equate_tycon_clo qenv rel dom clo0 clo1 =
  let x, qenv_x = extend qenv dom in
  let lazyx = LazyVal.make x in
  let clo0_x = Clo.inst rel clo0 (Val lazyx) in
  let clo1_x = Clo.inst rel clo1 (Val lazyx) in
  equate_tycon qenv_x rel clo0_x clo1_x

and equate_tycon_quantifier qenv rel quant0 quant1 =
  let dom = equate_tycon qenv rel (Val.unleash quant0.dom) (Val.unleash quant1.dom) in
  let cod = equate_tycon_clo qenv rel quant0.dom quant0.cod quant1.cod in
  dom, (Clo.name quant0.cod, cod)

and equate_tycon qenv rel ty0 ty1 =
  match ty0, ty1 with
  | Neu neu0, Neu neu1 ->
    equate_neutroid qenv rel neu0.neu neu1.neu

  | Pi pi0, Pi pi1 ->
    let dom, (nm, cod) = equate_tycon_quantifier qenv rel pi0 pi1 in
    Tm.pi nm dom cod

  | Sg sg0, Sg sg1 ->
    let dom, (nm, cod) = equate_tycon_quantifier qenv rel sg0 sg1 in
    Tm.sg nm dom cod

  | Ext extclo0, Ext extclo1 ->
    let nms = ExtClo.names extclo0 in
    let xs = Bwd.map Name.named nms in
    let qenv_xs = QEnv.abs xs qenv in
    let cells = Bwd.fold_right (fun x rs -> Dim (`Atom x) :: rs) xs [] in
    let ty0_xs, sys0_xs = ExtClo.inst rel extclo0 cells in
    let ty1_xs, sys1_xs = ExtClo.inst rel extclo1 cells in
    let ty_xs = equate_tycon qenv_xs rel ty0_xs ty1_xs in
    let sys_xs = equate_con_sys qenv_xs rel ty0_xs sys0_xs sys1_xs in
    Tm.make @@ Tm.Ext (Tm.NB (nms, (ty_xs, sys_xs)))

  | Restrict face0, Restrict face1 ->
    let face = equate_tycon_face qenv rel face0 face1 in
    Tm.make @@ Tm.Restrict face

  | V info0, V info1 ->
    let rel_r0 = Rel.equate' info0.r `Dim0 rel in
    let r = equate_dim qenv rel info0.r info1.r in
    let ty0 = equate_tyval qenv rel_r0 info0.ty0 info0.ty1 in
    let ty1 = equate_tyval qenv rel info0.ty1 info1.ty1 in
    let equiv_ty =
      let env =
        Env.init_isolated
          [Val (LazyVal.make @@ Val.unleash info0.ty1);
           Val (LazyVal.make @@ Val.unleash info0.ty0)]
      in
      Syn.eval rel_r0 env @@ Tm.equiv (Tm.up @@ Tm.ix 0) (Tm.up @@ Tm.ix 1)
    in
    let equiv = equate_val qenv rel_r0 equiv_ty info0.equiv info0.equiv in
    Tm.make @@ Tm.V {r; ty0; ty1; equiv}

  | HCom ({ty = `Pos; _} as hcom0), HCom ({ty = `Pos; _} as hcom1) ->
    let r = equate_dim qenv rel hcom0.r hcom1.r in
    let r' = equate_dim qenv rel hcom0.r' hcom1.r' in
    let cap = equate_tycon qenv rel (Val.unleash hcom0.cap) (Val.unleash hcom1.cap) in
    let sys = equate_tycon_abs_sys qenv rel hcom0.sys hcom1.sys in
    Tm.make @@ Tm.FHCom {r; r'; cap; sys}

  | Univ univ0, Univ univ1 ->
    if univ0.kind = univ1.kind && univ0.lvl = univ1.lvl then
      Tm.univ ~kind:univ0.kind ~lvl:univ0.lvl
    else
      raise PleaseRaiseProperError

  | Data data0, Data data1 when data0.lbl = data1.lbl ->
    let genv, _ = data0.constrs in
    let desc = GlobalEnv.lookup_datatype data0.lbl genv in
    let tyenv = Env.init genv in
    let params = equate_data_params qenv rel tyenv desc.body data0.params data1.params in
    Tm.make @@ Tm.Data {lbl = data0.lbl; params}

  | _ ->
    raise PleaseRaiseProperError

and equate_tyval qenv rel ty0 ty1 =
  equate_tycon qenv rel (Val.unleash ty0) (Val.unleash ty1)

and equate_con_abs qenv rel ty abs0 abs1 =
  let nm = let Abs (x, _) = abs0 in Name.name x in
  let x = Name.named nm in
  let qenv_x = QEnv.abs1 x qenv in
  let bdy0_x = ConAbs.inst rel abs0 (`Atom x) in
  let bdy1_x = ConAbs.inst rel abs1 (`Atom x) in
  let bdy_x = equate_con qenv_x rel ty bdy0_x bdy1_x in
  Tm.B (nm, bdy_x)

and equate_tycon_abs qenv rel abs0 abs1 =
  let nm = let Abs (x, _) = abs0 in Name.name x in
  let x = Name.named nm in
  let qenv_x = QEnv.abs1 x qenv in
  let bdy0_x = ConAbs.inst rel abs0 (`Atom x) in
  let bdy1_x = ConAbs.inst rel abs1 (`Atom x) in
  let bdy_x = equate_tycon qenv_x rel bdy0_x bdy1_x in
  Tm.B (nm, bdy_x)

and equate_tycon_abs_face qenv rel (r0, r'0, abs0) (r1, r'1, abs1) =
  let r = equate_dim qenv rel r0 r1 in
  let r' = equate_dim qenv rel r'0 r'1 in
  let rel = Rel.equate' r0 r'0 rel in
  let abs0 = LazyValAbs.unleash abs0 in
  let abs1 = LazyValAbs.unleash abs1 in
  r, r', Some (equate_tycon_abs qenv rel abs0 abs1)

and equate_con_abs_face qenv rel ty (r0, r'0, abs0) (r1, r'1, abs1) =
  let r = equate_dim qenv rel r0 r1 in
  let r' = equate_dim qenv rel r'0 r'1 in
  let rel = Rel.equate' r0 r'0 rel in
  let ty_rr' = Con.run rel ty in
  let abs0 = LazyValAbs.unleash abs0 in
  let abs1 = LazyValAbs.unleash abs1 in
  r, r', Some (equate_con_abs qenv rel ty_rr' abs0 abs1)

and equate_con_face qenv rel ty (r0, r'0, bdy0) (r1, r'1, bdy1) =
  let r = equate_dim qenv rel r0 r1 in
  let r' = equate_dim qenv rel r'0 r'1 in
  let rel = Rel.equate' r0 r'0 rel in
  let ty_rr' = Con.run rel ty in
  let bdy0 = LazyVal.unleash bdy0 in
  let bdy1 = LazyVal.unleash bdy1 in
  r, r', Some (equate_con qenv rel ty_rr' bdy0 bdy1)

and equate_tycon_face qenv rel (r0, r'0, bdy0) (r1, r'1, bdy1) =
  let r = equate_dim qenv rel r0 r1 in
  let r' = equate_dim qenv rel r'0 r'1 in
  let rel = Rel.equate' r0 r'0 rel in
  let bdy0 = LazyVal.unleash bdy0 in
  let bdy1 = LazyVal.unleash bdy1 in
  r, r', Some (equate_tycon qenv rel bdy0 bdy1)

and equate_sys_wrapper : 'a 'b. ('a -> 'a -> 'b) -> 'a list -> 'a list -> 'b list =
  fun face_equater sys0 sys1 ->
    try
      List.map2 face_equater sys0 sys1
    with
    | Invalid_argument _ ->
      raise PleaseRaiseProperError (* mismatched lengths *)

and equate_con_abs_sys qenv rel ty = equate_sys_wrapper (equate_con_abs_face qenv rel ty)
and equate_tycon_abs_sys qenv rel = equate_sys_wrapper (equate_tycon_abs_face qenv rel)
and equate_con_sys qenv rel ty = equate_sys_wrapper (equate_con_face qenv rel ty)

open RedBasis
open Bwd
open Domain

type step =
  | Ret : neu -> step
  | Step : value -> step

let ret v = Ret v
let step v = Step v


module type S =
sig
  val unleash : value -> con

  val reflect : value -> neu -> val_sys -> value

  val eval : env -> Tm.tm -> value
  val eval_cmd : env -> Tm.tm Tm.cmd -> value
  val eval_head : env -> Tm.tm Tm.head -> value
  val eval_frame : env -> value -> Tm.tm Tm.frame -> value
  val eval_dim : env -> Tm.tm -> I.t
  val eval_tick : env -> Tm.tm -> tick
  val eval_tm_sys : env -> (Tm.tm, Tm.tm) Tm.system -> val_sys
  val make_closure : env -> Tm.tm Tm.bnd -> clo

  val apply : value -> value -> value
  val ext_apply : value -> dim list -> value
  val prev : tick -> value -> value
  val car : value -> value
  val cdr : value -> value
  val lbl_call : value -> value
  val corestriction_force : value -> value


  val rigid_vproj : atom -> ty0:value -> ty1:value -> equiv:value -> el:value -> value

  val inst_clo : clo -> value -> value
  val inst_nclo : nclo -> value list -> value
  val inst_tick_clo : tick_clo -> tick -> value

  val unleash_pi : value -> value * clo
  val unleash_sg : value -> value * clo
  val unleash_v : value -> atom * value * value * value
  val unleash_later : value -> tick_clo
  val unleash_fcom : value -> dir * value * comp_sys
  val unleash_ext : value -> dim list -> value * val_sys
  val unleash_lbl_ty : value -> string * nf list * value
  val unleash_corestriction_ty : value -> val_face

  val base_restriction : Restriction.t

  module Macro : sig
    val equiv : value -> value -> value
  end

  module Error :
  sig
    type t
    val pp : t Pretty.t0
    exception E of t
  end
end

module type Sig =
sig
  val restriction : Restriction.t
  val global_dim : I.atom -> I.t
  val lookup : Name.t -> Tm.twin -> Tm.tm * (Tm.tm, Tm.tm) Tm.system
end

module M (Sig : Sig) : S =
struct
  let base_restriction = Sig.restriction


  exception ProjAbs of abs
  exception ProjVal of value


  type error =
    | UnexpectedEnvCell of env_el
    | ExpectedDimensionTerm of Tm.tm
    | ExpectedTickTerm of Tm.tm
    | InternalMortalityError
    | RigidCoeUnexpectedArgument of abs
    | RigidHComUnexpectedArgument of value
    | RigidGHComUnexpectedArgument of value
    | LblCallUnexpectedArgument of value
    | UnexpectedDimensionTerm of Tm.tm
    | UnexpectedTickTerm of Tm.tm
    | UnleashPiError of value
    | UnleashSgError of value
    | UnleashExtError of value
    | UnleashVError of value
    | UnleashLaterError of value
    | UnleashCoRError of value
    | UnleashLblTyError of value
    | UnleashFComError of value
    | ForcedUntrueCorestriction of val_face


  exception E of error

  let make_closure rho bnd =
    Clo {bnd; rho}

  let eval_dim rho tm =
    match Tm.unleash tm with
    | Tm.Dim0 ->
      `Dim0
    | Tm.Dim1 ->
      `Dim1
    | Tm.Up (hd, Emp) ->
      begin
        match hd with
        | Tm.Ix (i, _) ->
          begin
            match List.nth rho.cells i with
            | Atom x -> x
            | cell ->
              let err = UnexpectedEnvCell cell in
              raise @@ E err
          end

        | Tm.Var info ->
          I.act rho.global @@ Sig.global_dim info.name

        | Tm.Meta meta ->
          I.act rho.global @@ Sig.global_dim meta.name

        | _ ->
          let err = ExpectedDimensionTerm tm in
          raise @@ E err
      end
    | _ ->
      let err = ExpectedDimensionTerm tm in
      raise @@ E err

  let eval_tick rho tm =
    match Tm.unleash tm with
    | Tm.TickConst ->
      TickConst
    | Tm.Up (hd, Emp) ->
      begin
        match hd with
        | Tm.Ix (i, _) ->
          begin
            match List.nth rho.cells i with
            | Tick tck -> tck
            | cell ->
              let err = UnexpectedEnvCell cell in
              raise @@ E err
          end
        | Tm.Var info ->
          TickGen (`Global info.name)
        | _ ->
          let err = ExpectedTickTerm tm in
          raise @@ E err
      end
    | _ ->
      let err = ExpectedTickTerm tm in
      raise @@ E err




  let rec act_can phi con =
    match con with
    | Pi info ->
      let dom = Value.act phi info.dom in
      let cod = Clo.act phi info.cod in
      make @@ Pi {dom; cod}

    | Sg info ->
      let dom = Value.act phi info.dom in
      let cod = Clo.act phi info.cod in
      make @@ Sg {dom; cod}

    | Ext abs ->
      let abs' = ExtAbs.act phi abs in
      make @@ Ext abs'

    | Rst info ->
      let ty = Value.act phi info.ty in
      let sys = ValSys.act phi info.sys in
      make @@ Rst {ty; sys}

    | CoR face ->
      let face = ValFace.act phi face in
      make @@ CoR face

    | Coe info ->
      make_coe
        (Dir.act phi info.dir)
        (Abs.act phi info.abs)
        (Value.act phi info.el)

    | HCom info ->
      make_hcom
        (Dir.act phi info.dir)
        (Value.act phi info.ty)
        (Value.act phi info.cap)
        (CompSys.act phi info.sys)

    | GHCom info ->
      make_ghcom
        (Dir.act phi info.dir)
        (Value.act phi info.ty)
        (Value.act phi info.cap)
        (CompSys.act phi info.sys)

    | FCom info ->
      make_fcom
        (Dir.act phi info.dir)
        (Value.act phi info.cap)
        (CompSys.act phi info.sys)

    | Box info ->
      make_box
        (Dir.act phi info.dir)
        (Value.act phi info.cap)
        (BoxSys.act phi info.sys)

    | V info ->
      make_v phi
        (I.act phi @@ `Atom info.x)
        (fun phi0 -> Value.act phi0 info.ty0)
        (Value.act phi info.ty1)
        (fun phi0 -> Value.act phi0 info.equiv)

    | VIn info ->
      make_vin phi
        (I.act phi @@ `Atom info.x)
        (fun phi0 -> Value.act phi0 info.el0)
        (Value.act phi info.el1)

    | Univ _ ->
      make con

    | Bool ->
      make con

    | Tt ->
      make con

    | Ff ->
      make con

    | Nat ->
      make con

    | Zero ->
      make con

    | Suc n ->
      make @@ Suc (Value.act phi n)

    | Int ->
      make con

    | Pos n ->
      make @@ Pos (Value.act phi n)

    | NegSuc n ->
      make @@ NegSuc (Value.act phi n)

    | S1 ->
      make con

    | Base ->
      make con

    | Loop x ->
      make_loop @@ I.act phi @@ `Atom x

    | Lam clo ->
      make @@ Lam (Clo.act phi clo)

    | ExtLam abs ->
      make @@ ExtLam (Abs.act phi abs)

    | CoRThunk v ->
      make @@ CoRThunk (ValFace.act phi v)

    | Cons (v0, v1) ->
      make @@ Cons (Value.act phi v0, Value.act phi v1)

    | LblTy {lbl; ty; args} ->
      make @@ LblTy {lbl; ty = Value.act phi ty; args = List.map (act_nf phi) args}

    | LblRet v ->
      make @@ LblRet (Value.act phi v)

    | Up info ->
      let ty = Value.act phi info.ty in
      let sys = ValSys.act phi @@ ValSys.from_rigid info.sys in
      begin
        match force_val_sys sys with
        | `Proj v -> v
        | `Ok sys ->
          match act_neu phi info.neu with
          | Ret neu ->
            make @@ Up {ty; neu; sys}
          | Step v ->
            v
      end

    | Later clo ->
      make @@ Later (TickClo.act phi clo)

    | Next clo ->
      make @@ Next (TickClo.act phi clo)

    | DFix info ->
      let ty = Value.act phi info.ty in
      let clo = Clo.act phi info.clo in
      make @@ DFix {ty; clo}

    | DFixLine info ->
      let r = I.act phi @@ `Atom info.x in
      let ty = Value.act phi info.ty in
      let clo = Clo.act phi info.clo in
      make_dfix_line r ty clo

  and act_neu phi con =
    match con with
    | VProj info ->
      let mx = I.act phi @@ `Atom info.x in
      let ty0 phi0 = Value.act phi0 info.ty0 in
      let ty1 = Value.act phi info.ty1 in
      let equiv phi0 = Value.act phi0 info.equiv in
      begin
        match act_neu phi info.neu with
        | Ret neu ->
          let vty = make_v phi mx ty0 ty1 equiv in
          let el = make @@ Up {ty = vty; neu = neu; sys = []} in
          step @@ vproj phi mx ~ty0 ~ty1 ~equiv ~el
        | Step el ->
          step @@ vproj phi mx ~ty0 ~ty1 ~equiv ~el
      end

    | Cap info ->
      let mdir = Dir.act phi info.dir in
      let msys = CompSys.act phi info.sys in
      begin
        match act_neu phi info.neu with
        | Ret neu ->
          (* this is dumb; should refactor this with `cap`. *)
          let el = make @@ Up {ty = info.ty; neu; sys = []} in
          step @@ make_cap mdir info.ty msys el
        | Step el ->
          step @@ make_cap mdir info.ty msys el
      end

    | FunApp (neu, arg) ->
      let varg = act_nf phi arg in
      begin
        match act_neu phi neu with
        | Ret neu ->
          ret @@ FunApp (neu, varg)
        | Step v ->
          let {el; _} = varg in
          step @@ apply v el
      end

    | ExtApp (neu, rs) ->
      let rs = List.map (I.act phi) rs in
      begin
        match act_neu phi neu with
        | Ret neu ->
          ret @@ ExtApp (neu, rs)
        | Step v ->
          step @@ ext_apply v rs
      end

    | Car neu ->
      begin
        match act_neu phi neu with
        | Ret neu ->
          ret @@ Car neu
        | Step v ->
          step @@ car v
      end

    | Cdr neu ->
      begin
        match act_neu phi neu with
        | Ret neu ->
          ret @@ Cdr neu
        | Step v ->
          step @@ cdr v
      end

    | If info ->
      let mot = Clo.act phi info.mot in
      let tcase = Value.act phi info.tcase in
      let fcase = Value.act phi info.fcase in
      begin
        match act_neu phi info.neu with
        | Ret neu ->
          ret @@ If {mot; neu; tcase; fcase}
        | Step v ->
          step @@ if_ mot v tcase fcase
      end

    | NatRec info ->
      let mot = Clo.act phi info.mot in
      let zcase = Value.act phi info.zcase in
      let scase = NClo.act phi info.scase in
      begin
        match act_neu phi info.neu with
        | Ret neu ->
          ret @@ NatRec {mot; neu; zcase; scase}
        | Step v ->
          step @@ nat_rec mot v zcase scase
      end

    | IntRec info ->
      let mot = Clo.act phi info.mot in
      let pcase = Clo.act phi info.pcase in
      let ncase = Clo.act phi info.ncase in
      begin
        match act_neu phi info.neu with
        | Ret neu ->
          ret @@ IntRec {mot; neu; pcase; ncase}
        | Step v ->
          step @@ int_rec mot v pcase ncase
      end

    | S1Rec info ->
      let mot = Clo.act phi info.mot in
      let bcase = Value.act phi info.bcase in
      let lcase = Abs.act phi info.lcase in
      begin
        match act_neu phi info.neu with
        | Ret neu ->
          ret @@ S1Rec {mot; neu; bcase; lcase}
        | Step v ->
          step @@ s1_rec mot v bcase lcase
      end

    | LblCall neu ->
      begin
        match act_neu phi neu with
        | Ret neu ->
          ret @@ LblCall neu
        | Step v ->
          step @@ lbl_call v
      end

    | CoRForce neu ->
      begin
        match act_neu phi neu with
        | Ret neu ->
          ret @@ CoRForce neu
        | Step v ->
          step @@ corestriction_force v
      end

    | Lvl _ ->
      ret con

    | Var _ ->
      ret con

    | Meta _ ->
      ret con

    | Prev (tick, neu) ->
      begin
        match act_neu phi neu with
        | Ret neu ->
          ret @@ Prev (tick, neu)
        | Step v ->
          step @@ prev tick v
      end

    | Fix (tick, ty, clo) ->
      ret @@ Fix (tick, Value.act phi ty, Clo.act phi clo)

    | FixLine (x, tick, ty, clo) ->
      let ty' = Value.act phi ty in
      let clo' = Clo.act phi clo in
      begin
        match I.act phi @@ `Atom x with
        | `Atom y ->
          ret @@ FixLine (y, tick, ty', clo')
        | `Dim0 ->
          ret @@ Fix (tick, ty', clo')
        | `Dim1 ->
          (* TODO: check that this is right *)
          step @@ inst_clo clo' @@ make @@ DFix {ty = ty'; clo = clo'}
      end

  and act_nf phi (nf : nf) =
    match nf with
    | info ->
      let ty = Value.act phi info.ty in
      let el = Value.act phi info.el in
      {ty; el}

  and force_abs_face face =
    match face with
    | Face.True (_, _, abs) ->
      raise @@ ProjAbs abs
    | Face.False _ -> None
    | Face.Indet (xi, abs) ->
      Some (Face.Indet (xi, abs))

  and force_val_face (face : val_face) =
    match face with
    | Face.True (_, _, v) ->
      raise @@ ProjVal v
    | Face.False _ -> None
    | Face.Indet (xi, v) ->
      Some (Face.Indet (xi, v))

  and force_val_sys sys =
    try
      `Ok (Option.filter_map force_val_face sys)
    with
    | ProjVal v ->
      `Proj v

  and force_abs_sys sys =
    try
      `Ok (Option.filter_map force_abs_face sys)
    with
    | ProjAbs abs ->
      `Proj abs

  and unleash : value -> con =
    fun (Node info) ->
      let con =
        match info.action = I.idn with
        | true ->
          run_dfcon info.con
        | false ->
          let node' = act_can info.action @@ run_dfcon info.con in
          let con = unleash node' in
          con
      in
      match con with
      | Up up ->
        begin
          match unleash up.ty with
          | Rst rst ->
            begin
              match force_val_sys rst.sys with
              | `Proj el ->
                unleash el
              | `Ok sys ->
                Up {ty = rst.ty; neu = up.neu; sys}
            end
          | _ ->
            con
        end
      | _ ->
        con

  and run_dfcon =
    function
    | Con con ->
      con
    | Reflect info ->
      unleash @@ reflect info.ty info.neu info.sys

  and make_cons (a, b) = make @@ Cons (a, b)

  and make_extlam abs = make @@ ExtLam abs

  and make_dfix_line r ty clo =
    match r with
    | `Atom x ->
      make @@ DFixLine {x; ty; clo}
    | `Dim0 ->
      make @@ DFix {ty; clo}
    | `Dim1 ->
      let bdy = inst_clo clo @@ make @@ DFix {ty; clo} in
      let tclo = TickCloConst bdy in
      make @@ Next tclo

  and make_v phi r ty0 ty1 equiv : value =
    match r with
    | `Atom x ->
      let phi0 = I.cmp (I.equate r `Dim0) phi in
      make @@ V {x; ty0 = ty0 phi0; ty1; equiv = equiv phi0}
    | `Dim0 ->
      ty0 phi
    | `Dim1 ->
      ty1

  and make_vin phi mgen el0 el1 : value =
    match mgen with
    | `Atom x ->
      let phi0 = I.cmp (I.equate mgen `Dim0) phi in
      rigid_vin x (el0 phi0) el1
    | `Dim0 ->
      el0 phi
    | `Dim1 ->
      el1

  and make_loop mx : value =
    match mx with
    | `Atom x ->
      rigid_loop x
    | _ ->
      make @@ Base

  and make_coe mdir abs el : value =
    match mdir with
    | `Ok dir ->
      rigid_coe dir abs el
    | `Same _ ->
      el

  and make_hcom mdir ty cap msys : value =
    match mdir with
    | `Ok dir ->
      begin
        match msys with
        | `Ok sys ->
          rigid_hcom dir ty cap sys
        | `Proj abs ->
          let _, r' = Dir.unleash dir in
          Abs.inst1 abs r'
      end
    | `Same _ ->
      cap

  and make_ghcom mdir ty cap msys : value =
    match mdir with
    | `Ok dir ->
      begin
        match msys with
        | `Ok sys ->
          rigid_ghcom dir ty cap sys
        | `Proj abs ->
          let _, r' = Dir.unleash dir in
          Abs.inst1 abs r'
      end
    | `Same _ ->
      cap

  and make_com mdir abs cap msys : value =
    match mdir with
    | `Ok dir ->
      let _, r' = Dir.unleash dir in
      begin
        match msys with
        | `Ok sys ->
          rigid_com dir abs cap sys
        | `Proj abs ->
          Abs.inst1 abs r'
      end
    | `Same _ ->
      cap

  and make_gcom mdir abs cap msys : value =
    match mdir with
    | `Ok dir ->
      let _, r' = Dir.unleash dir in
      begin
        match msys with
        | `Ok sys ->
          rigid_gcom dir abs cap sys
        | `Proj abs ->
          Abs.inst1 abs r'
      end
    | `Same _ ->
      cap

  and make_fcom mdir cap msys : value =
    match mdir with
    | `Ok dir ->
      begin
        match msys with
        | `Ok sys ->
          rigid_fcom dir cap sys
        | `Proj abs ->
          let _, r' = Dir.unleash dir in
          Abs.inst1 abs r'
      end
    | `Same _ ->
      cap

  and make_box mdir cap msys : value =
    match mdir with
    | `Ok dir ->
      begin
        match msys with
        | `Ok sys ->
          rigid_box dir cap sys
        | `Proj el ->
          el
      end
    | `Same _ ->
      cap

  and rigid_vin x el0 el1 : value =
    make @@ VIn {x; el0; el1}

  and rigid_loop x : value =
    make @@ Loop x

  and rigid_coe dir abs el =
    let x, tyx = Abs.unleash1 abs in
    match unleash tyx with
    | (Pi _ | Sg _ | Ext _ | Up _ | Later _) ->
      make @@ Coe {dir; abs; el}

    | (Bool | Univ _) ->
      el

    | FCom fcom ->
      (* [F]: favonia 11.00100100001111110110101010001000100001011.
       * [SVO]: Part III (airport).
       * [R1]: RedPRL I ddcc4ce72b1880671d842ede6b50adbee94935b5.
       * [Y]: yacctt 073694948042342d55cea64a42d2076365800ee4. *)

      (* Some helper functions to reduce typos. *)
      let r, r' = Dir.unleash dir in
      let s, s' = Dir.unleash fcom.dir in
      let cap_abs = Abs.bind1 x fcom.cap in
      let subst_r = I.subst r x in
      let subst_r' = I.subst r' x in

      (* This is O in [SVO, F].
       *
       * The purpose of O is to make sure that, when r=r', we can recover the coercee
       * after the long journey detailed below. *)
      let origin phi z_dest =
        let face =
          Face.map @@ fun sj s'j absj ->
          let phi = I.cmp (I.equate sj s'j) phi in
          Abs.make1 @@ fun y ->
          make_coe (Dir.make (`Atom y) (I.act (I.cmp phi subst_r) s)) absj @@
          make_coe (Dir.make (I.act (I.cmp phi subst_r) s') (`Atom y)) absj @@
          (Value.act phi el)
        in
        make_hcom
          (Dir.make (I.act (I.cmp phi subst_r) s') z_dest)
          (Value.act (I.cmp phi subst_r) fcom.cap)
          (make_cap
             (Dir.act (I.cmp phi subst_r) fcom.dir)
             (Value.act (I.cmp phi subst_r) fcom.cap)
             (CompSys.act (I.cmp phi subst_r) fcom.sys)
             (Value.act phi el))
          (force_abs_sys @@ List.map (fun b -> face (AbsFace.act (I.cmp phi subst_r) b)) fcom.sys)
      in
      (* This is N in [F, SVO], representing the coherence conditions enforced by `fcom.sys`.
       * The coercion must be equal to the coercion within the system under the restriction.
       *
       * Precondition: `x` is apart from `phi` (thus `subst_x` commutes with `phi`),
       *   but `x` may appear in `z_dest`.
       *
       * It turns out `I.act subst_x z_dest` is always `z_dest` at the call sites, but maybe it is
       * safer to do substitution every time. *)
      let recovery_apart phi abs x_dest z_dest =
        let subst_x = I.subst x_dest x in
        make_coe (Dir.make (I.act (I.cmp subst_x phi) s') (I.act subst_x z_dest)) abs @@
        make_coe (Dir.make (I.act phi r) x_dest) (Abs.bind1 x @@ Abs.inst1 abs (I.act phi s')) @@
        Value.act phi el
      in
      (* This is P in [F, SVO], the naive coercion of the cap part of the box within `fcom.cap`.
       * The problem is that we do not have the boundaries of the box, and even if we have,
       * this naive cap will not be the image of the boundaries. *)
      let naively_coerced_cap phi =
        make_gcom (Dir.act phi dir) (Abs.act phi cap_abs) (origin phi (I.act (I.cmp phi subst_r) s)) @@
        force_abs_sys @@
        let diag =
          if I.absent x s && I.absent x s'
          then [
            AbsFace.make phi (I.act phi s) (I.act phi s') @@ fun phi ->
            Abs.bind1 x @@ make_coe (Dir.make (I.act phi r) (`Atom x)) (Abs.act phi cap_abs) (Value.act phi el)
          ]
          else []
        in
        let face =
          (* assuming x is apart from ri and r'i *)
          Face.map @@ fun sj s'j absj ->
          let phi = I.cmp (I.equate sj s'j) phi in
          Abs.bind1 x @@ recovery_apart phi absj (`Atom x) (I.act phi s)
        in
        diag @ List.map (fun b -> face (AbsFace.act phi b)) (CompSys.forall x fcom.sys)
      in
      (* This is Q in [F, SVO]. This is used to calculate the preimage of the naively coerced cap
       * for the boundaries and the fixed cap.
       *
       * For equations apart from `x`, the recovery_general will coincide with recovery_apart.
       * This optimization is automatic thanks to the semantic simplification in redtt. *)
      let recovery_general phi abs z_dest =
        make_gcom (Dir.make (I.act (I.cmp phi subst_r') s) z_dest) abs (naively_coerced_cap phi) @@
        force_abs_sys @@
        let diag = AbsFace.make phi (I.act phi r) (I.act phi r') @@ fun phi ->
          Abs.make1 @@ fun y -> recovery_apart phi (Abs.act phi abs) (I.act phi r) (`Atom y) in
        let face =
          Face.map @@ fun sj s'j absj ->
          let phi = I.cmp (I.equate sj s'j) phi in
          Abs.make1 @@ fun y -> recovery_apart phi absj (I.act phi r') (`Atom y)
        in
        diag :: List.map (fun b -> face (AbsFace.act phi b)) (CompSys.forall x fcom.sys)
      in
      (* This is the "cap" part of the final request in [F, SVO].
       *
       * Using Q, the preimages, this is to calculate the final cap based on the naive cap. *)
      let coerced_cap =
        make_hcom (Dir.act subst_r' fcom.dir) (Value.act subst_r' fcom.cap) (naively_coerced_cap I.idn) @@
        force_abs_sys @@
        let diag = AbsFace.make_from_dir I.idn dir @@ fun phi ->
          Abs.make1 @@ fun w -> origin phi (`Atom w) in
        let face = Face.map @@ fun sj s'j absj ->
          let phi = I.equate sj s'j in
          Abs.make1 @@ fun w ->
          make_coe (Dir.make (`Atom w) (I.act phi (I.act subst_r' s))) absj @@
          recovery_general phi absj (`Atom w)
        in
        diag :: List.map (fun b -> face (AbsFace.act subst_r' b)) fcom.sys
      in
      make_box (Dir.act subst_r' fcom.dir) coerced_cap @@
      force_val_sys @@
      let face = Face.map @@ fun sj s'j absj ->
        let phi = I.equate sj s'j in
        recovery_general phi absj (I.act (I.cmp phi subst_r') s')
      in List.map (fun b -> face (AbsFace.act subst_r' b)) fcom.sys


    | V info ->
      (* [F]: favonia 11.00100100001111110110101010001000100001011.
       * [SVO]: Part III (airport).
       * [R1]: RedPRL I ddcc4ce72b1880671d842ede6b50adbee94935b5.
       * [Y]: yacctt 073694948042342d55cea64a42d2076365800ee4. *)

      (* Some helper functions to reduce typos. *)
      let r, r' = Dir.unleash dir in
      let abs0 = Abs.bind1 x info.ty0 in
      let abs1 = Abs.bind1 x info.ty1 in
      let subst_0 = Value.act (I.subst `Dim0 x) in
      let subst_r' = Value.act (I.subst r' x) in
      let ty00 = subst_0 info.ty0 in
      let ty10 = subst_0 info.ty1 in
      let equiv0 = subst_0 info.equiv in
      begin
        match info.x = x with
        | true ->
          (* `base` is the cap of the hcom in ty1.
           * Due to the eager semantic simplification built in
           * `vproj`, `make_coe` and `make_hcom`,
           * redtt can afford less efficient generating code. *)
          let base phi src dest =
            make_coe (Dir.make src dest) (Abs.act phi abs1) @@
            let subst_src = Value.act (I.subst src x) in
            vproj phi
              (I.act phi src)
              ~ty0:(fun phi0 -> Value.act phi0 @@ subst_src info.ty0)
              ~ty1:(Value.act phi @@ subst_src info.ty1)
              ~equiv:(fun phi0 -> Value.act phi0 @@ subst_src info.equiv)
              ~el:(Value.act phi el)
          in
          (* Some helper functions to reduce typos. *)
          let base0 phi dest = base phi `Dim0 dest in
          let base1 phi dest = base phi `Dim1 dest in
          let fiber0 phi b = car @@ apply (cdr (Value.act phi equiv0)) b in
          (* This gives a path from the fiber `fib` to `fiber0 b`
           * where `b` is calculated from `fib` as
           * `ext_apply (cdr fib) [`Dim1]` directly. *)
          let contr0 phi fib = apply (cdr @@ apply (cdr (Value.act phi equiv0)) (ext_apply (cdr fib) [`Dim1])) fib in
          (* The diagonal face for r=r'. *)
          let face_diag = AbsFace.make_from_dir I.idn dir @@ fun phi ->
            Abs.make1 @@ fun _ -> base phi (I.act phi r) (I.act phi r')
          in
          (* The face for r=0. *)
          let face0 = AbsFace.make I.idn r `Dim0 @@ fun phi ->
            Abs.make1 @@ fun _ -> base0 phi (I.act phi r')
          in
          (* The face for r=1. This more optimized version is used
           * in [Y], [F] and [R1] but not [SVO]. *)
          let face1 = AbsFace.make I.idn r `Dim1 @@ fun phi ->
            Abs.make1 @@ fun y ->
            let ty = Value.act phi @@ subst_r' info.ty1 in
            let cap = base1 phi (I.act phi r') in
            let msys = force_abs_sys @@
              let face0 = AbsFace.make phi (I.act phi r') `Dim0 @@ fun phi ->
                Abs.make1 @@ fun z -> ext_apply (cdr (fiber0 phi cap)) [`Atom z]
              in
              let face1 = AbsFace.make phi (I.act phi r') `Dim1 @@ fun phi ->
                Abs.make1 @@ fun _ -> Value.act phi el in
              [face0; face1]
            in
            make_hcom (Dir.make `Dim1 (`Atom y)) ty cap msys
          in
          (* This is the type of the fiber, and is used for
           * simplifying the generating code for the front face
           * (r'=0). It is using the evaluator to generate the
           * type in the semantic domain. *)
          let fiber0_ty phi b =
            let var i = Tm.up @@ Tm.ix i in
            eval (Env.push_many [Val (Value.act phi ty00); Val (Value.act phi ty10); Val (car (Value.act phi equiv0)); Val b] Env.emp) @@
            Tm.Macro.fiber ~ty0:(var 0) ~ty1:(var 1) ~f:(var 2) ~x:(var 3)
          in
          (* This is to generate the element in `ty0` and also
           * the face for r'=0. This is `O` in [F]. *)
          let fixer_fiber phi =
            (* Turns out `fiber_at_face0` will be
             * used for multiple times. *)
            let fiber_at_face0 phi = make_cons
                (Value.act phi el, make_extlam @@ Abs.make1 @@ fun _ -> base0 phi `Dim0)
            in
            let mode = `UNIFORM_HCOM in (* how should we switch this? *)
            match mode with
            (* The implementation used in [F] and [R1]. *)
            | `SPLIT_COERCION ->
              begin
                match r with
                | `Dim0 -> fiber_at_face0 phi (* r=0 *)
                | `Dim1 -> fiber0 phi (base1 phi `Dim0) (* r=1 *)
                | `Atom r_atom ->
                  (* XXX This needs to be updated with the new Thought. *)
                  (* coercion to the diagonal *)
                  let path_in_fiber0_ty =
                    contr0 phi @@
                    make_coe (Dir.make `Dim0 (I.act phi r)) (Abs.bind1 r_atom (fiber0_ty phi (base phi (I.act phi r) `Dim0))) @@
                    (* the fiber *)
                    make_cons (Value.act (I.cmp phi (I.subst `Dim0 r_atom)) el, make_extlam @@ Abs.make1 @@ fun _ -> base0 phi `Dim0)
                  in
                  ext_apply path_in_fiber0_ty [r]
              end
            (* The implementation used in [Y]. *)
            | `UNIFORM_HCOM ->
              (* hcom whore cap is (fiber0 base), r=0 face is contr0, and r=1 face is constant *)
              make_hcom (Dir.make `Dim1 `Dim0) (fiber0_ty phi (base phi (I.act phi r) `Dim0)) (fiber0 phi (base phi (I.act phi r) `Dim0)) @@
              force_abs_sys @@
              let face0 = AbsFace.make phi (I.act phi r) `Dim0 @@ fun phi ->
                Abs.make1 @@ fun w -> ext_apply (contr0 phi (fiber_at_face0 phi)) [`Atom w]
              in
              let face1 = AbsFace.make phi (I.act phi r) `Dim1 @@ fun phi ->
                Abs.make1 @@ fun _ -> fiber0 phi (base1 phi `Dim0)
              in
              [face0; face1]
            (* Something magical under development. *)
            | `UNICORN ->
              raise @@ E InternalMortalityError
          in
          let el0 phi0 =
            try
              car (fixer_fiber phi0)
            with
            | exn ->
              (* Format.eprintf "Not immortal enough: %a@." pp_value (fixer_fiber phi0); *)
              raise exn
          in
          let face_front =
            AbsFace.make I.idn r' `Dim0 @@ fun phi ->
            Abs.make1 @@ fun w -> ext_apply (cdr (fixer_fiber phi)) [`Atom w]
          in
          let el1 = make_hcom (Dir.make `Dim1 `Dim0) info.ty1 (base I.idn r r') @@
            force_abs_sys [face0; face1; face_diag; face_front]
          in
          make_vin I.idn r' el0 el1

        | false ->
          let el0 =
            let phi0 = I.equate (`Atom info.x) `Dim0 in
            make_coe (Dir.act phi0 dir) (Abs.act phi0 abs0) (Value.act phi0 el)
          in
          let el1 =
            let cap =
              let phi = I.subst r x in
              let ty0r = Value.act phi info.ty0 in
              let ty1r = Value.act phi info.ty1 in
              let equivr = Value.act phi info.equiv in
              rigid_vproj info.x ~ty0:ty0r ~ty1:ty1r ~equiv:equivr ~el
            in
            let mode = `INCONSISTENCY_REMOVAL in
            let sys =
              let face0 =
                AbsFace.gen_const I.idn info.x `Dim0 @@ fun phi ->
                Abs.bind1 x @@ apply (car info.equiv) @@
                make_coe (Dir.make (I.act phi r) (`Atom x)) (Abs.act phi abs0) (Value.act phi el)
              in
              let face1 =
                AbsFace.gen_const I.idn info.x `Dim1 @@ fun phi ->
                Abs.bind1 x @@
                make_coe (Dir.make (I.act phi r) (`Atom x)) (Abs.act phi abs1) (Value.act phi el)
              in
              match mode with
              | `OLD_SCHOOL -> Option.filter_map force_abs_face [face0; face1]
              | `INCONSISTENCY_REMOVAL -> Option.filter_map force_abs_face [face0]
              | `UNICORN -> raise @@ E InternalMortalityError
            in
            rigid_com dir abs1 cap sys
          in
          rigid_vin info.x el0 el1
      end

    | _ ->
      let err = RigidCoeUnexpectedArgument abs in
      raise @@ E err

  and rigid_hcom dir ty cap sys : value =
    match unleash ty with
    | (Pi _ | Sg _ | Ext _ | Up _) ->
      make @@ HCom {dir; ty; cap; sys}

    | Bool | Nat | Int ->
      cap

    | S1 ->
      make @@ FCom {dir; cap; sys}

    | Univ _ ->
      rigid_fcom dir cap sys

    | FCom fcom ->
      (* [F]: favonia 11.00100100001111110110101010001000100001011.
       * [SVO]: Part III (airport).
       * [R1]: RedPRL I ddcc4ce72b1880671d842ede6b50adbee94935b5.
       * [Y]: yacctt 073694948042342d55cea64a42d2076365800ee4. *)

      (* The algorithm is based on the Anders' alternative hcom in [F]. *)

      (* Helper functions. *)
      let r, r' = Dir.unleash dir in
      let _, s' = Dir.unleash fcom.dir in

      (* This is C_M in [F], with an extra parameter `phi` to get along with NbE. *)
      let cap_aux phi el = make_cap
          (Dir.act phi fcom.dir) (Value.act phi fcom.cap) (CompSys.act phi fcom.sys) el
      in

      (* This serves as `O` and the diagonal face in [F]
       * for the coherence conditions in `fcom.sys` and `s=s'`. *)
      let hcom_template phi y_dest ty = make_hcom
          (Dir.make (I.act phi r) y_dest) ty
          (Value.act phi fcom.cap) (CompSys.act phi fcom.sys)
      in

      (* This is `P` in [F]. *)
      let new_cap = rigid_hcom dir fcom.cap (cap_aux I.idn cap) @@
        let ri_faces =
          let face = Face.map @@ fun ri r'i abs ->
            let y, el = Abs.unleash1 abs in
            Abs.bind1 y (cap_aux (I.equate ri r'i) el)
          in
          List.map face sys
        in
        let si_faces =
          let face = Face.map @@ fun si s'i abs ->
            let phi = I.equate si s'i in
            Abs.make1 @@ fun y ->
            (* this is not the most efficient code, but maybe we can afford this? *)
            cap_aux phi (hcom_template phi (`Atom y) (Value.act phi (Abs.inst1 abs s')))
          in
          List.map face fcom.sys
        in
        let diag = AbsFace.make_from_dir I.idn fcom.dir @@ fun phi ->
          Abs.make1 @@ fun y -> hcom_template phi (`Atom y) (Value.act phi fcom.cap)
        in
        Option.filter_map force_abs_face [diag] @ (ri_faces @ si_faces)
      in
      let boundary = Face.map @@ fun si s'i abs ->
        let phi = I.equate si s'i in
        hcom_template phi (I.act phi r') (Value.act phi (Abs.inst1 abs s'))
      in
      rigid_box fcom.dir new_cap
        (List.map boundary fcom.sys)

    | V {x; ty0; ty1; equiv} ->
      let r, _ = Dir.unleash dir in
      let el0 =
        let phi0 = I.equate (`Atom x) `Dim0 in
        make_hcom (Dir.act phi0 dir) ty0 (Value.act phi0 cap) (CompSys.act phi0 sys)
      in
      let el1 =
        let hcom phi x_dest ty = make_hcom (Dir.make (I.act phi r) x_dest) ty (Value.act phi cap) (CompSys.act phi sys) in
        let face0 =
          AbsFace.gen_const I.idn x `Dim0 @@ fun phi ->
          Abs.make1 @@ fun y ->
          apply (car (Value.act phi equiv)) @@
          hcom phi (`Atom y) ty0 (* ty0 is already under `phi0` *)
        in
        let face1 =
          AbsFace.gen_const I.idn x `Dim1 @@ fun phi ->
          Abs.make1 @@ fun y ->
          hcom phi (`Atom y) (Value.act phi ty1)
        in
        let el1_cap = rigid_vproj x ~ty0 ~ty1 ~equiv ~el:cap in
        let el1_sys =
          let face =
            Face.map @@ fun ri r'i absi ->
            let phi = I.equate ri r'i in
            let phi0 = I.cmp (I.equate (`Atom x) `Dim0) phi in
            let yi, el = Abs.unleash absi in
            Abs.bind yi @@ rigid_vproj x ~ty0:(Value.act phi0 ty0) ~ty1:(Value.act phi ty1) ~equiv:(Value.act phi0 equiv) ~el
          in
          Option.filter_map force_abs_face [face0; face1] @ List.map face sys
        in
        rigid_hcom dir ty1 el1_cap el1_sys
      in
      rigid_vin x el0 el1

    | _ ->
      let err = RigidHComUnexpectedArgument ty in
      raise @@ E err

  and rigid_ghcom dir ty cap sys : value =
    match unleash ty with
    (* Who knows whether we can delay the expansion
     * in `Up _`? Please move `Up _` to the second
     * list if this does not work out. *)
    | (Pi _ | Sg _ | Up _) ->
      make @@ GHCom {dir; ty; cap; sys}

    (* `Ext _`: the expansion will stop after a valid
     * correction system, so it is not so bad. *)
    | (Ext _ | Bool | Univ _ | FCom _ | V _) ->
      let aux sys =
        match sys with
        | [] -> cap
        | Face.Indet (eqi, absi) :: rest ->
          let ri, r'i = Eq.unleash eqi in
          let r, r' = Dir.unleash dir in
          let face (dim0, dim1) =
            AbsFace.make I.idn ri dim0 @@ fun phi ->
            (* XXX this would stop the expansion early, but is
             * unfortunately duplicate under `AbsFace.make` *)

            (* TODO: it is entirely possible that this equation is inconsistent, so we would raise an exception here. - Jon *)
            match CompSys.act phi rest with
            | `Proj abs -> abs
            | `Ok rest0 ->
              let r'i = I.act phi r'i in
              let ghcom00 = AbsFace.make phi r'i dim0 @@ fun phi -> Abs.act phi absi in
              let ghcom01 = AbsFace.make phi r'i dim1 @@ fun phi ->
                Abs.make1 @@ fun y ->
                (* TODO this can be optimized further by expanding
                 * `make_ghcom` because `ty` is not changed and
                 * in degenerate cases there is redundant renaming. *)
                make_ghcom (Dir.make (I.act phi r) (`Atom y)) (Value.act phi ty) (Value.act phi cap) @@
                (* XXX this would stop the expansion early, but is
                 * unfortunately duplicate under `AbsFace.make` *)
                CompSys.act phi rest0
              in
              match force_abs_sys [ghcom00; ghcom01] with
              | `Proj abs -> abs
              | `Ok faces ->
                Abs.make1 @@ fun y ->
                make_hcom (Dir.make (I.act phi r) (`Atom y)) (Value.act phi ty) (Value.act phi cap) (`Ok (faces @ rest))
          in
          let face0 = face (`Dim0, `Dim1) in
          let face1 = face (`Dim1, `Dim0) in
          match force_abs_sys [face0; face1] with
          | `Proj abs -> Abs.inst1 abs r'
          | `Ok faces -> rigid_hcom dir ty cap (faces @ sys)
      in
      aux sys

    | _ ->
      let err = RigidGHComUnexpectedArgument ty in
      raise @@ E err

  and rigid_com dir abs cap (sys : comp_sys) : value =
    let _, r' = Dir.unleash dir in
    let ty = Abs.inst1 abs r' in
    let capcoe = rigid_coe dir abs cap in
    let syscoe : comp_sys =
      let face =
        Face.map @@ fun ri r'i absi ->
        let phi = I.equate ri r'i in
        let yi, vi = Abs.unleash1 absi in
        let y2r' = Dir.make (`Atom yi) (I.act phi r') in
        Abs.bind1 yi @@ make_coe y2r' (Abs.act phi abs) vi
      in
      List.map face sys
    in
    rigid_hcom dir ty capcoe syscoe

  and rigid_gcom dir abs cap (sys : comp_sys) : value =
    let _, r' = Dir.unleash dir in
    let ty = Abs.inst1 abs r' in
    let capcoe = rigid_coe dir abs cap in
    let syscoe : comp_sys =
      let face =
        Face.map @@ fun ri r'i absi ->
        let phi = I.equate ri r'i in
        let yi, vi = Abs.unleash1 absi in
        let y2r' = Dir.make (`Atom yi) (I.act phi r') in
        Abs.bind1 yi @@ make_coe y2r' (Abs.act phi abs) vi
      in
      List.map face sys
    in
    rigid_ghcom dir ty capcoe syscoe

  and rigid_fcom dir cap sys : value =
    make @@ FCom {dir; cap; sys}

  and rigid_box dir cap sys : value =
    make @@ Box {dir; cap; sys}


  and clo bnd rho =
    Clo {bnd; rho}

  and nclo nbnd rho =
    NClo {nbnd; rho}

  and eval (rho : env) tm =
    match Tm.unleash tm with
    | Tm.Pi (dom, cod) ->
      let dom = eval rho dom in
      let cod = clo cod rho in
      make @@ Pi {dom; cod}

    | Tm.Sg (dom, cod) ->
      let dom = eval rho dom in
      let cod = clo cod rho in
      make @@ Sg {dom; cod}

    | Tm.Ext bnd ->
      let abs = eval_ext_bnd rho bnd in
      make @@ Ext abs

    | Tm.Rst info ->
      let ty = eval rho info.ty in
      let sys = eval_tm_sys rho info.sys in
      make @@ Rst {ty; sys}

    | Tm.CoR tface ->
      let face = eval_tm_face rho tface in
      make @@ CoR face

    | Tm.V info ->
      let r = eval_dim rho info.r in
      let ty0 phi0 = eval (Env.act phi0 rho) info.ty0 in
      let ty1 = eval rho info.ty1 in
      let equiv phi0 = eval (Env.act phi0 rho) info.equiv in
      make_v I.idn r ty0 ty1 equiv

    | Tm.VIn info ->
      let r = eval_dim rho info.r in
      let el0 phi0 = eval (Env.act phi0 rho) info.tm0 in
      let el1 = eval rho info.tm1 in
      make_vin I.idn r el0 el1

    | Tm.Lam bnd ->
      make @@ Lam (clo bnd rho)

    | Tm.ExtLam bnd ->
      let abs = eval_nbnd rho bnd in
      make @@ ExtLam abs

    | Tm.CoRThunk face ->
      let vface = eval_tm_face rho face in
      make @@ CoRThunk vface

    | Tm.Cons (t0, t1) ->
      let v0 = eval rho t0 in
      let v1 = eval rho t1 in
      make @@ Cons (v0, v1)

    | Tm.FCom info ->
      let r = eval_dim rho info.r  in
      let r' = eval_dim rho info.r' in
      let dir = Dir.make r r' in
      let cap = eval rho info.cap in
      let sys = eval_rigid_bnd_sys rho info.sys in
      make_fcom dir cap sys

    | Tm.Univ {kind; lvl} ->
      make @@ Univ {kind; lvl}

    | Tm.Bool ->
      make Bool

    | Tm.Tt ->
      make Tt

    | Tm.Ff ->
      make Ff

    | Tm.Nat ->
      make Nat

    | Tm.Zero ->
      make Zero

    | Tm.Suc n ->
      let n = eval rho n in
      make @@ Suc n

    | Tm.Int ->
      make Int

    | Tm.Pos n ->
      let n = eval rho n in
      make @@ Pos n

    | Tm.NegSuc n ->
      let n = eval rho n in
      make @@ NegSuc n

    | Tm.S1 ->
      make S1

    | Tm.Base ->
      make Base

    | Tm.Loop r ->
      make_loop @@ eval_dim rho r

    | Tm.Box info ->
      let r = eval_dim rho info.r  in
      let r' = eval_dim rho info.r' in
      let dir = Dir.make r r' in
      let cap = eval rho info.cap in
      let sys = eval_rigid_tm_sys rho info.sys in
      make_box dir cap sys

    | (Tm.Dim0 | Tm.Dim1) ->
      raise @@ E (UnexpectedDimensionTerm tm)

    | Tm.TickConst ->
      raise @@ E (UnexpectedTickTerm tm)

    | Tm.Up cmd ->
      eval_cmd rho cmd

    | Tm.Let (cmd, Tm.B (_, t)) ->
      let v0 = eval_cmd rho cmd in
      eval (Env.push (Val v0) rho) t

    | Tm.LblTy info ->
      let ty = eval rho info.ty in
      let args = List.map (fun (ty, tm) -> {ty = eval rho ty; el = eval rho tm}) info.args in
      make @@ LblTy {lbl = info.lbl; ty; args}

    | Tm.LblRet t ->
      make @@ LblRet (eval rho t)

    | Tm.Later bnd ->
      let tclo = TickClo {bnd; rho} in
      make @@ Later tclo

    | Tm.Next bnd ->
      let tclo = TickClo {bnd; rho} in
      make @@ Next tclo

  and eval_cmd rho (hd, sp) =
    let vhd = eval_head rho hd in
    eval_stack rho vhd @@ Bwd.to_list sp

  and eval_stack rho vhd =
    function
    | [] -> vhd
    | frm :: stk ->
      let vhd = eval_frame rho vhd frm in
      eval_stack rho vhd stk

  and eval_frame rho vhd =
    function
    | Tm.LblCall ->
      lbl_call vhd
    | Tm.CoRForce ->
      corestriction_force vhd
    | Tm.FunApp t ->
      let v = eval rho t in
      apply vhd v
    | Tm.ExtApp ts ->
      let rs = List.map (eval_dim rho) ts in
      ext_apply vhd rs
    | Tm.Car ->
      car vhd
    | Tm.Cdr ->
      cdr vhd
    | Tm.VProj info ->
      let r = eval_dim rho info.r in
      let ty0 phi0 = eval (Env.act phi0 rho) info.ty0 in
      let ty1 = eval rho info.ty1 in
      let equiv phi0 = eval (Env.act phi0 rho) info.equiv in
      vproj I.idn r ~ty0 ~ty1 ~equiv ~el:vhd
    | Tm.If info ->
      let mot = clo info.mot rho in
      let tcase = eval rho info.tcase in
      let fcase = eval rho info.fcase in
      if_ mot vhd tcase fcase
    | Tm.NatRec info ->
      let mot = clo info.mot rho in
      let zcase = eval rho info.zcase in
      let scase = nclo info.scase rho in
      nat_rec mot vhd zcase scase
    | Tm.IntRec info ->
      let mot = clo info.mot rho in
      let pcase = clo info.pcase rho in
      let ncase = clo info.ncase rho in
      int_rec mot vhd pcase ncase
    | Tm.S1Rec info ->
      let mot = clo info.mot rho in
      let bcase = eval rho info.bcase in
      let lcase = eval_bnd rho info.lcase in
      s1_rec mot vhd bcase lcase
    | Tm.Cap info ->
      let r = eval_dim rho info.r in
      let r' = eval_dim rho info.r' in
      let dir = Dir.make r r' in
      let ty = eval rho info.ty in
      let sys = eval_rigid_bnd_sys rho info.sys in
      make_cap dir ty sys vhd
    | Tm.Prev tick ->
      let vtick = eval_tick rho tick in
      prev vtick vhd



  and eval_head rho =
    function
    | Tm.Down info ->
      eval rho info.tm

    | Tm.DFix info ->
      let r = eval_dim rho info.r in
      let ty = eval rho info.ty in
      let clo = clo info.bdy rho in
      make_dfix_line r ty clo

    | Tm.Coe info ->
      let r = eval_dim rho info.r in
      let r' = eval_dim rho info.r' in
      let dir = Dir.make r r' in
      let abs = eval_bnd rho info.ty  in
      let el = eval rho info.tm in
      make_coe dir abs el

    | Tm.HCom info ->
      let r = eval_dim rho info.r in
      let r' = eval_dim rho info.r' in
      let dir = Dir.make r r' in
      let ty = eval rho info.ty in
      let cap = eval rho info.cap in
      let sys = eval_rigid_bnd_sys rho info.sys in
      make_hcom dir ty cap sys

    | Tm.Com info ->
      let r = eval_dim rho info.r in
      let r' = eval_dim rho info.r' in
      let dir = Dir.make r r' in
      let abs = eval_bnd rho info.ty in
      let cap = eval rho info.cap in
      let sys = eval_rigid_bnd_sys rho info.sys in
      make_com dir abs cap sys

    | Tm.GHCom info ->
      let r = eval_dim rho info.r in
      let r' = eval_dim rho info.r' in
      let dir = Dir.make r r' in
      let ty = eval rho info.ty in
      let cap = eval rho info.cap in
      let sys = eval_rigid_bnd_sys rho info.sys in
      make_ghcom dir ty cap sys

    | Tm.GCom info ->
      let r = eval_dim rho info.r in
      let r' = eval_dim rho info.r' in
      let dir = Dir.make r r' in
      let abs = eval_bnd rho info.ty in
      let cap = eval rho info.cap in
      let sys = eval_rigid_bnd_sys rho info.sys in
      make_gcom dir abs cap sys

    | Tm.Ix (i, _) ->
      begin
        match List.nth rho.cells i with
        | Val v -> v
        | cell ->
          let err = UnexpectedEnvCell cell in
          raise @@ E err
      end

    | Tm.Var info ->
      let tty, tsys = Sig.lookup info.name info.twin in
      let rho' = Env.clear_locals rho in
      let vsys = eval_tm_sys rho' @@ Tm.map_tm_sys (Tm.shift_univ info.ushift) tsys in
      let vty = eval rho' @@ Tm.shift_univ info.ushift tty in
      reflect vty (Var {name = info.name; twin = info.twin; ushift = info.ushift}) vsys

    | Tm.Meta {name; ushift} ->
      let tty, tsys = Sig.lookup name `Only in
      let rho' = Env.clear_locals rho in
      let vsys = eval_tm_sys rho' @@ Tm.map_tm_sys (Tm.shift_univ ushift) tsys in
      let vty = eval rho' @@ Tm.shift_univ ushift tty in
      reflect vty (Meta {name; ushift}) vsys

  and reflect ty neu sys =
    match force_val_sys sys with
    | `Proj el -> el
    | `Ok sys ->
      make @@ Up {ty; neu; sys}

  and eval_bnd_face rho (tr, tr', obnd) =
    let sr = eval_dim rho tr in
    let sr' = eval_dim rho tr' in
    match Eq.make sr sr' with
    | `Ok xi ->
      let bnd = Option.get_exn obnd in
      let rho' = Env.act (I.equate sr sr') rho in
      let abs = eval_bnd rho' bnd in
      Face.Indet (xi, abs)
    | `Apart _ ->
      Face.False (sr, sr')
    | `Same _ ->
      let bnd = Option.get_exn obnd in
      let abs = eval_bnd rho bnd in
      Face.True (sr, sr', abs)

  and eval_rigid_bnd_sys rho sys  =
    try
      let sys =
        Option.filter_map
          (fun x -> force_abs_face @@ eval_bnd_face rho x)
          sys
      in `Ok sys
    with
    | ProjAbs abs ->
      `Proj abs

  and eval_tm_face rho (tr, tr', otm) : val_face =
    let r = eval_dim rho tr in
    let r' = eval_dim rho tr' in
    match Eq.make r r' with
    | `Ok xi ->
      let tm = Option.get_exn otm in
      let rho' = Env.act (I.equate r r') rho in
      (* The problem here is that the this is not affecting GLOBALS! *)
      let el = eval rho' tm in
      Face.Indet (xi, el)
    | `Apart _ ->
      Face.False (r, r')
    | `Same _ ->
      let tm = Option.get_exn otm in
      let el = eval rho tm in
      Face.True (r, r', el)

  and eval_tm_sys rho sys : val_sys =
    List.map (eval_tm_face rho) sys

  and eval_rigid_tm_sys rho sys  =
    try
      let sys =
        Option.filter_map
          (fun x -> force_val_face @@ eval_tm_face rho x)
          sys
      in `Ok sys
    with
    | ProjVal tm ->
      `Proj tm

  and eval_bnd rho bnd =
    let Tm.B (_, tm) = bnd in
    let x = Name.fresh () in
    let rho = Env.push (Atom (`Atom x)) rho in
    Abs.bind1 x @@ eval rho tm

  and eval_nbnd rho bnd =
    let Tm.NB (nms, tm) = bnd in
    let xs = Bwd.map Name.named nms in
    let rho = Env.push_many (List.rev @@ Bwd.to_list @@ Bwd.map (fun x -> Atom (`Atom x)) xs) rho in
    Abs.bind xs @@ eval rho tm

  and eval_ext_bnd rho bnd =
    let Tm.NB (nms, (tm, sys)) = bnd in
    let xs = Bwd.map Name.named nms in
    let rho = Env.push_many (List.rev @@ Bwd.to_list @@ Bwd.map (fun x -> Atom (`Atom x)) xs) rho in
    ExtAbs.bind xs (eval rho tm, eval_tm_sys rho sys)

  and unleash_pi v =
    match unleash v with
    | Pi {dom; cod} -> dom, cod
    | Rst rst -> unleash_pi rst.ty
    | _ ->
      raise @@ E (UnleashPiError v)


  and unleash_later v =
    match unleash v with
    | Later clo -> clo
    | Rst rst -> unleash_later rst.ty
    | _ ->
      raise @@ E (UnleashLaterError v)

  and unleash_sg v =
    match unleash v with
    | Sg {dom; cod} -> dom, cod
    | Rst rst -> unleash_sg rst.ty
    | _ ->
      raise @@ E (UnleashSgError v)

  and unleash_ext v rs =
    match unleash v with
    | Ext abs ->
      ExtAbs.inst abs (Bwd.from_list rs)
    | Rst rst ->
      unleash_ext rst.ty rs
    | _ ->
      raise @@ E (UnleashExtError v)

  and unleash_v v =
    match unleash v with
    | V {x; ty0; ty1; equiv} ->
      x, ty0, ty1, equiv
    | Rst rst ->
      unleash_v rst.ty
    | _ ->
      raise @@ E (UnleashVError v)

  and unleash_fcom v =
    match unleash v with
    | FCom info -> info.dir, info.cap, info.sys
    | Rst rst -> unleash_fcom rst.ty
    | _ ->
      raise @@ E (UnleashFComError v)

  and unleash_lbl_ty v =
    match unleash v with
    | LblTy {lbl; args; ty} ->
      lbl, args, ty
    | Rst rst ->
      unleash_lbl_ty rst.ty
    | _ ->
      raise @@ E (UnleashLblTyError v)

  and unleash_corestriction_ty v =
    match unleash v with
    | CoR face ->
      face
    | Rst rst ->
      unleash_corestriction_ty rst.ty
    | _ ->
      raise @@ E (UnleashCoRError v)

  and lbl_call v =
    match unleash v with
    | LblRet v -> v
    | Up info ->
      let _, _, ty = unleash_lbl_ty info.ty in
      let call = LblCall info.neu in
      let call_face =
        Face.map @@ fun _ _ a ->
        lbl_call a
      in
      let call_sys = List.map call_face info.sys in
      make @@ Up {ty; neu = call; sys = call_sys}
    | _ ->
      raise @@ E (LblCallUnexpectedArgument v)

  and corestriction_force v =
    match unleash v with
    | CoRThunk face ->
      begin
        match face with
        | Face.True (_, _, v) -> v
        | _ ->
          raise @@ E (ForcedUntrueCorestriction face)
      end

    | Up info ->
      begin
        match unleash_corestriction_ty info.ty with
        | Face.True (_, _, ty) ->
          let force = CoRForce info.neu in
          let force_face =
            Face.map @@ fun _ _ a ->
            corestriction_force a
          in
          let force_sys = List.map force_face info.sys in
          make @@ Up {ty; neu = force; sys = force_sys}
        | _ as face ->
          raise @@ E (ForcedUntrueCorestriction face)
      end

    | _ ->
      failwith "corestriction_force"

  and apply vfun varg =
    match unleash vfun with
    | Lam clo ->
      inst_clo clo varg

    | Up info ->
      let dom, cod = unleash_pi info.ty in
      let cod' = inst_clo cod varg in
      let app = FunApp (info.neu, {ty = dom; el = varg}) in
      let app_face =
        Face.map @@ fun r r' a ->
        apply a @@ Value.act (I.equate r r') varg
      in
      let app_sys = List.map app_face info.sys in
      make @@ Up {ty = cod'; neu = app; sys = app_sys}

    | Coe info ->
      let r, r' = Dir.unleash info.dir in
      let x, tyx = Abs.unleash1 info.abs in
      let domx, codx = unleash_pi tyx in
      let dom = Abs.bind1 x domx in
      let coe_r'_x = make_coe (Dir.make r' (`Atom x)) dom varg in
      let cod_coe = inst_clo codx coe_r'_x in
      let abs = Abs.bind1 x cod_coe in
      let el =
        apply info.el @@
        make_coe
          (Dir.make r' r)
          dom
          varg
      in
      rigid_coe info.dir abs el

    | HCom info ->
      let _, cod = unleash_pi info.ty in
      let ty = inst_clo cod varg in
      let cap = apply info.cap varg in
      let app_face =
        Face.map @@ fun r r' abs ->
        let x, v = Abs.unleash1 abs in
        Abs.bind1 x @@ apply v (Value.act (I.equate r r') varg)
      in
      let sys = List.map app_face info.sys in
      rigid_hcom info.dir ty cap sys

    | GHCom info ->
      let _, cod = unleash_pi info.ty in
      let ty = inst_clo cod varg in
      let cap = apply info.cap varg in
      let app_face =
        Face.map @@ fun r r' abs ->
        let x, v = Abs.unleash1 abs in
        Abs.bind1 x @@ apply v (Value.act (I.equate r r') varg)
      in
      let sys = List.map app_face info.sys in
      rigid_ghcom info.dir ty cap sys

    | _ ->
      failwith "apply"

  and ext_apply vext (ss : I.t list) =
    match unleash vext with
    | ExtLam abs ->
      Abs.inst abs (Bwd.from_list ss)

    | Up info ->
      let tyr, sysr = unleash_ext info.ty ss in
      begin
        match force_val_sys sysr with
        | `Ok sysr ->
          let app = ExtApp (info.neu, ss) in
          let app_face =
            Face.map @@ fun r r' a ->
            ext_apply a @@ List.map (I.act (I.equate r r')) ss
          in
          let app_sys = List.map app_face info.sys in
          make @@ Up {ty = tyr; neu = app; sys = sysr @ app_sys}
        | `Proj v ->
          v
      end

    | Coe info ->
      let y, ext_y = Abs.unleash1 info.abs in
      let ty_s, sys_s = unleash_ext ext_y ss in
      let forall_y_sys_s = ValSys.forall y sys_s in
      begin
        match force_val_sys forall_y_sys_s with
        | `Proj v ->
          v

        | `Ok rsys ->
          let correction =
            let face = Face.map @@ fun _ _ v -> Abs.bind1 y v in
            List.map face rsys
          in
          let abs = Abs.bind1 y ty_s in
          let cap = ext_apply info.el ss in
          rigid_com info.dir abs cap correction
      end

    | HCom info ->
      let ty_s, sys_s = unleash_ext info.ty ss in
      begin
        match force_val_sys sys_s with
        | `Proj v ->
          v
        | `Ok boundary_sys ->
          let cap = ext_apply info.cap ss in
          let correction_sys =
            let face = Face.map @@ fun _ _ v -> Abs.make1 @@ fun _ -> v in
            List.map face boundary_sys
          in
          let comp_sys =
            let face =
              Face.map @@ fun r r' abs ->
              let phi_rr' = I.equate r r' in
              let ss_rr' = List.map (I.act phi_rr') ss in
              let x, v = Abs.unleash1 abs in
              Abs.bind1 x @@ ext_apply v ss_rr'
            in
            List.map face info.sys
          in
          rigid_hcom info.dir ty_s cap @@ correction_sys @ comp_sys
      end

    | _ ->
      failwith "ext_apply"

  and prev tick el =
    match unleash el with
    | Next tclo ->
      inst_tick_clo tclo tick
    | DFix dfix ->
      begin
        match tick with
        | TickConst ->
          inst_clo dfix.clo el
        | TickGen gen ->
          let neu = Fix (gen, dfix.ty, dfix.clo) in
          make @@ Up {ty = dfix.ty; neu; sys = []}
      end
    | DFixLine dfix ->
      begin
        match tick with
        | TickConst ->
          inst_clo dfix.clo el
        | TickGen gen ->
          let neu = FixLine (dfix.x, gen, dfix.ty, dfix.clo) in
          make @@ Up {ty = dfix.ty; neu; sys = []}
      end

    | Up info ->
      let tclo = unleash_later info.ty in
      let ty = inst_tick_clo tclo tick in
      let prev_face =
        Face.map @@ fun _ _ a ->
        prev tick a
      in
      let prev_sys = List.map prev_face info.sys in
      make @@ Up {ty; neu = Prev (tick, info.neu); sys = prev_sys}

    | Coe info ->
      (* EXPERIMENTAL !!! *)
      let x, tyx = Abs.unleash1 info.abs in
      let tclox = unleash_later tyx in
      let cod_tick = inst_tick_clo tclox tick in
      let abs = Abs.bind1 x cod_tick in
      let el = prev tick info.el in
      rigid_coe info.dir abs el

    | HCom info ->
      (* EXPERIMENTAL !!! *)
      let tclo = unleash_later info.ty in
      let ty = inst_tick_clo tclo tick in
      let cap = prev tick info.cap in
      let prev_face =
        Face.map @@ fun _ _ abs ->
        let x, v = Abs.unleash1 abs in
        Abs.bind1 x @@ prev tick v
      in
      let sys = List.map prev_face info.sys in
      rigid_hcom info.dir ty cap sys

    | GHCom info ->
      (* EXPERIMENTAL !!! *)
      let tclo = unleash_later info.ty in
      let ty = inst_tick_clo tclo tick in
      let cap = prev tick info.cap in
      let prev_face =
        Face.map @@ fun _ _ abs ->
        let x, v = Abs.unleash1 abs in
        Abs.bind1 x @@ prev tick v
      in
      let sys = List.map prev_face info.sys in
      rigid_ghcom info.dir ty cap sys

    | _ ->
      failwith "prev"


  (* the equation oracle `phi` is for continuations `ty0` and `equiv`
   * waiting for an updated oracle. *)
  and vproj phi mgen ~ty0 ~ty1 ~equiv ~el : value =
    match mgen with
    | `Atom x ->
      let phi0 = I.cmp (I.equate mgen `Dim0) phi in
      rigid_vproj x ~ty0:(ty0 phi0) ~ty1 ~equiv:(equiv phi0) ~el
    | `Dim0 ->
      let func = car (equiv phi) in
      apply func el
    | `Dim1 ->
      el

  and rigid_vproj x ~ty0 ~ty1 ~equiv ~el : value =
    match unleash el with
    | VIn info ->
      info.el1
    | Up up ->
      let neu = VProj {x; ty0; ty1; equiv; neu = up.neu} in
      let vproj_face =
        Face.map @@ fun r r' a ->
        let phi = I.equate r r' in
        vproj phi (I.act phi @@ `Atom x) ~ty0:(fun phi0 -> Value.act phi0 ty0) ~ty1:(Value.act phi ty1) ~equiv:(fun phi0 -> Value.act phi0 equiv) ~el:a
      in
      let vproj_sys = List.map vproj_face up.sys in
      make @@ Up {ty = ty1; neu; sys = vproj_sys}
    | _ ->
      failwith "rigid_vproj"

  and if_ mot scrut tcase fcase =
    match unleash scrut with
    | Tt ->
      tcase
    | Ff ->
      fcase
    | Up up ->
      let neu = If {mot; neu = up.neu; tcase; fcase} in
      let mot' = inst_clo mot scrut in
      let if_face =
        Face.map @@ fun r r' a ->
        let phi = I.equate r r' in
        if_ (Clo.act phi mot) a (Value.act phi tcase) (Value.act phi fcase)
      in
      let if_sys = List.map if_face up.sys in
      make @@ Up {ty = mot'; neu; sys = if_sys}
    | _ ->
      failwith "if_"

  and nat_rec mot scrut zcase scase =
    match unleash scrut with
    | Zero ->
      zcase
    | Suc n ->
      let n_rec = nat_rec mot n zcase scase in
      inst_nclo scase @@ [n; n_rec]
    | Up up ->
      let neu = NatRec {mot; neu = up.neu; zcase; scase} in
      let mot' = inst_clo mot scrut in
      let nat_rec_face =
        Face.map @@ fun r r' a ->
        let phi = I.equate r r' in
        nat_rec (Clo.act phi mot) a (Value.act phi zcase) (NClo.act phi scase)
      in
      let nat_rec_sys = List.map nat_rec_face up.sys in
      make @@ Up {ty = mot'; neu; sys = nat_rec_sys}
    | _ ->
      failwith "nat_rec"

  and int_rec mot scrut pcase ncase =
    match unleash scrut with
    | Pos n -> inst_clo pcase n
    | NegSuc n -> inst_clo ncase n
    | Up up ->
      let neu = IntRec {mot; neu = up.neu; pcase; ncase} in
      let mot' = inst_clo mot scrut in
      let int_rec_face =
        Face.map @@ fun r r' a ->
        let phi = I.equate r r' in
        int_rec (Clo.act phi mot) a (Clo.act phi pcase) (Clo.act phi ncase)
      in
      let int_rec_sys = List.map int_rec_face up.sys in
      make @@ Up {ty = mot'; neu; sys = int_rec_sys}
    | _ ->
      failwith "int_rec"

  and s1_rec mot scrut bcase lcase =
    match unleash scrut with
    | Base ->
      bcase
    | Loop x ->
      Abs.inst1 lcase @@ `Atom x
    | FCom info ->
      let apply_rec tm = s1_rec mot tm bcase lcase in
      let r, _ = Dir.unleash info.dir in
      let ty = Abs.make1 @@ fun y ->
        inst_clo mot @@
        make_fcom (Dir.make r (`Atom y)) info.cap (`Ok info.sys)
      in
      let face = Face.map @@ fun ri r'i absi ->
        let y, el = Abs.unleash1 absi in
        Abs.bind1 y @@ Value.act (I.equate ri r'i) @@ apply_rec el
      in
      rigid_com info.dir ty (apply_rec info.cap) (List.map face info.sys)
    | Up up ->
      let neu = S1Rec {mot; neu = up.neu; bcase; lcase} in
      let mot' = inst_clo mot scrut in
      let s1_rec_face =
        Face.map @@ fun r r' a ->
        let phi = I.equate r r' in
        s1_rec (Clo.act phi mot) a (Value.act phi bcase) (Abs.act phi lcase)
      in
      let s1_rec_sys = List.map s1_rec_face up.sys in
      make @@ Up {ty = mot'; neu; sys = s1_rec_sys}
    | _ ->
      failwith "s1_rec"

  and car v =
    match unleash v with
    | Cons (v0, _) ->
      v0

    | Up info ->
      let dom, _ = unleash_sg info.ty in
      let car_sys = List.map (Face.map (fun _ _ a -> car a)) info.sys in
      make @@ Up {ty = dom; neu = Car info.neu; sys = car_sys}

    | Coe info ->
      let x, tyx = Abs.unleash1 info.abs in
      let domx, _ = unleash_sg tyx in
      let abs = Abs.bind1 x domx in
      let el = car info.el in
      rigid_coe info.dir abs el

    | HCom info ->
      let dom, _ = unleash_sg info.ty in
      let cap = car info.cap in
      let face =
        Face.map @@ fun _ _ abs ->
        let y, v = Abs.unleash1 abs in
        Abs.bind1 y @@ car v
      in
      let sys = List.map face info.sys in
      rigid_hcom info.dir dom cap sys

    | GHCom info ->
      let dom, _ = unleash_sg info.ty in
      let cap = car info.cap in
      let face =
        Face.map @@ fun _ _ abs ->
        let y, v = Abs.unleash1 abs in
        Abs.bind1 y @@ car v
      in
      let sys = List.map face info.sys in
      rigid_ghcom info.dir dom cap sys

    | _ ->
      failwith "car"

  and cdr v =
    match unleash v with
    | Cons (_, v1) ->
      v1

    | Up info ->
      let _, cod = unleash_sg info.ty in
      let cdr_sys = List.map (Face.map (fun _ _ a -> cdr a)) info.sys in
      let cod_car = inst_clo cod @@ car v in
      make @@ Up {ty = cod_car; neu = Cdr info.neu; sys = cdr_sys}

    | Coe info ->
      let abs =
        let x, tyx = Abs.unleash1 info.abs in
        let domx, codx = unleash_sg tyx in
        let r, _ = Dir.unleash info.dir in
        let coerx =
          make_coe
            (Dir.make r (`Atom x))
            (Abs.bind1 x domx)
            (car info.el)
        in
        Abs.bind1 x @@ inst_clo codx coerx
      in
      let el = cdr info.el in
      rigid_coe info.dir abs el

    | HCom info ->
      let abs =
        let r, _ = Dir.unleash info.dir in
        let dom, cod = unleash_sg info.ty in
        let z = Name.fresh () in
        let msys =
          let face =
            Face.map @@ fun _ _ absi ->
            let yi, vi = Abs.unleash absi in
            Abs.bind yi @@ car vi
          in
          `Ok (List.map face info.sys)
        in
        let hcom =
          make_hcom
            (Dir.make r (`Atom z))
            dom
            (car info.cap)
            msys
        in
        Abs.bind1 z @@ inst_clo cod hcom
      in
      let cap = cdr info.cap in
      let sys =
        let face =
          Face.map @@ fun _ _ absi ->
          let yi, vi = Abs.unleash absi in
          Abs.bind yi @@ cdr vi
        in
        List.map face info.sys
      in
      rigid_com info.dir abs cap sys

    | GHCom info ->
      let abs =
        let r, _ = Dir.unleash info.dir in
        let dom, cod = unleash_sg info.ty in
        let z = Name.fresh () in
        let msys =
          let face =
            Face.map @@ fun _ _ absi ->
            let yi, vi = Abs.unleash absi in
            Abs.bind yi @@ car vi
          in
          `Ok (List.map face info.sys)
        in
        let hcom =
          make_ghcom
            (Dir.make r (`Atom z))
            dom
            (car info.cap)
            msys
        in
        Abs.bind1 z @@ inst_clo cod hcom
      in
      let cap = cdr info.cap in
      let sys =
        let face =
          Face.map @@ fun _ _ absi ->
          let yi, vi = Abs.unleash absi in
          Abs.bind yi @@ cdr vi
        in
        List.map face info.sys
      in
      rigid_gcom info.dir abs cap sys

    | _ ->
      failwith "cdr"

  and make_cap mdir ty msys el : value =
    match mdir with
    | `Ok dir ->
      begin
        match msys with
        | `Ok sys ->
          rigid_cap dir ty sys el
        | `Proj abs ->
          rigid_coe (Dir.swap dir) abs el
      end
    | `Same _ ->
      el

  and rigid_cap dir ty sys el : value =
    match unleash el with
    | Box info -> info.cap
    | Up info ->
      let cap_sys = List.map (Face.map (fun ri r'i a ->
          let phi = I.equate ri r'i in
          make_cap (Dir.act phi dir) (Value.act phi ty) (CompSys.act phi sys) a)) info.sys in
      make @@ Up {ty; neu = Cap {dir; neu = info.neu; ty; sys}; sys = cap_sys}
    | _ ->
      failwith "rigid_cap"


  and inst_clo clo varg =
    match clo with
    | Clo info ->
      let Tm.B (_, tm) = info.bnd in
      eval (Env.push (Val varg) info.rho) tm

  and inst_nclo nclo vargs =
    match nclo with
    | NClo info ->
      let Tm.NB (_, tm) = info.nbnd in
      (* Reversing makes sense here because: the left-most element of the environment is the innermost variable *)
      eval (Env.push_many (List.rev_map (fun v -> Val v) vargs) info.rho) tm

  and inst_tick_clo clo tick =
    match clo with
    | TickClo info ->
      let Tm.B (_, tm) = info.bnd in
      eval (Env.push (Tick tick) info.rho) tm
    | TickCloConst v ->
      v

  module Macro =
  struct
    let equiv ty0 ty1 : value =
      let rho = Env.push_many [Val ty0; Val ty1] Env.emp in
      eval rho @@
      Tm.Macro.equiv
        (Tm.up @@ Tm.ix 0)
        (Tm.up @@ Tm.ix 1)

  end


  module Error =
  struct
    type t = error

    let pp fmt =
      function
      | InternalMortalityError ->
        Format.fprintf fmt "Too mortal, taste it!"
      | RigidCoeUnexpectedArgument abs ->
        Format.fprintf fmt
          "Unexpected type argument in rigid coercion: %a."
          pp_abs abs
      | RigidHComUnexpectedArgument v ->
        Format.fprintf fmt
          "Unexpected type argument in rigid homogeneous copmosition: %a."
          pp_value v
      | RigidGHComUnexpectedArgument v ->
        Format.fprintf fmt
          "Unexpected type argument in rigid generalized homogeneous copmosition: %a."
          pp_value v
      | LblCallUnexpectedArgument v ->
        Format.fprintf fmt
          "Unexpected argument to labeled type projection: %a"
          pp_value v
      | UnexpectedEnvCell _ ->
        Format.fprintf fmt
          "Did not find what was expected in the environment"
      | ExpectedDimensionTerm t ->
        Format.fprintf fmt
          "Tried to evaluate non-dimension term %a as dimension."
          Tm.pp0 t
      | ExpectedTickTerm t ->
        Format.fprintf fmt
          "Tried to evaluate non-tick term %a as dimension."
          Tm.pp0 t
      | UnexpectedDimensionTerm t ->
        Format.fprintf fmt
          "Tried to evaluate dimension term %a as expression."
          Tm.pp0 t
      | UnexpectedTickTerm t ->
        Format.fprintf fmt
          "Tried to evaluate tick term %a as expression."
          Tm.pp0 t
      | UnleashPiError v ->
        Format.fprintf fmt
          "Tried to unleash %a as pi type."
          pp_value v
      | UnleashSgError v ->
        Format.fprintf fmt
          "Tried to unleash %a as sigma type."
          pp_value v
      | UnleashVError v ->
        Format.fprintf fmt
          "Tried to unleash %a as V type."
          pp_value v
      | UnleashLaterError v ->
        Format.fprintf fmt
          "Tried to unleash %a as later modality."
          pp_value v
      | UnleashExtError v ->
        Format.fprintf fmt
          "Tried to unleash %a as extension type."
          pp_value v
      | UnleashCoRError v ->
        Format.fprintf fmt
          "Tried to unleash %a as co-restriction type."
          pp_value v
      | UnleashFComError v ->
        Format.fprintf fmt
          "Tried to unleash %a as formal homogeneous composition."
          pp_value v
      | UnleashLblTyError v ->
        Format.fprintf fmt
          "Tried to unleash %a as labeled type."
          pp_value v
      | ForcedUntrueCorestriction face ->
        Format.fprintf fmt
          "Cannot force untrue co-restriction: %a"
          pp_val_face face




    exception E = E

    let _ =
      PpExn.install_printer @@ fun fmt ->
      function
      | E err ->
        pp fmt err
      | _ ->
        raise PpExn.Unrecognized

  end

end

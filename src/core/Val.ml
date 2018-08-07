open RedBasis
open Bwd
open BwdNotation
open Domain

include ValSig

module B = Desc.Boundary

type step =
  | Ret : neu -> step
  | Step : value -> step

let ret v = Ret v
let step v = Step v


type error =
  | UnexpectedEnvCell of env_el
  | ExpectedDimensionTerm of Tm.tm
  | ExpectedTickTerm of Tm.tm
  | InternalMortalityError
  | RigidCoeUnexpectedArgument of abs
  | RigidHComUnexpectedArgument of value
  | RigidGHComUnexpectedArgument of value
  | ApplyUnexpectedFunction of value
  | ApplyUnexpectedCube of value
  | RecursorUnexpectedArgument of string * value
  | SigmaProjUnexpectedArgument of string * value
  | RigidVProjUnexpectedArgument of value
  | RigidCapUnexpectedArgument of value
  | LblCallUnexpectedArgument of value
  | UnexpectedDimensionTerm of Tm.tm
  | UnexpectedTickTerm of Tm.tm
  | UnleashDataError of value
  | UnleashPiError of value
  | UnleashSgError of value
  | UnleashExtError of value
  | UnleashVError of value
  | UnleashLaterError of value
  | UnleashBoxModalityError of value
  | UnleashCoRError of value
  | UnleashLblTyError of value
  | UnleashFHComError of value
  | ForcedUntrueCorestriction of val_face
  | ForcedUnexpectedCorestriction of value


exception E of error

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
        "Unexpected type argument in rigid homogeneous composition:@ %a."
        pp_value v
    | RigidGHComUnexpectedArgument v ->
      Format.fprintf fmt
        "Unexpected type argument in rigid generalized homogeneous composition:@ %a."
        pp_value v
    | ApplyUnexpectedFunction v ->
      Format.fprintf fmt
        "Apply unexpected function:@ %a."
        pp_value v
    | ApplyUnexpectedCube v ->
      Format.fprintf fmt
        "Apply unexpected line or higher-dimensional cube:@ %a."
        pp_value v
    | RecursorUnexpectedArgument (ty, v) ->
      Format.fprintf fmt
        "Unexpected argument to the recursor of %s:@ %a."
        ty pp_value v
    | SigmaProjUnexpectedArgument (proj, v) ->
      Format.fprintf fmt
        "Unexpected argument to Sigma type projection %s:@ %a."
        proj pp_value v
    | RigidVProjUnexpectedArgument v ->
      Format.fprintf fmt
        "Unexpected argument to rigid vproj:@ %a."
        pp_value v
    | RigidCapUnexpectedArgument v ->
      Format.fprintf fmt
        "Unexpected argument to rigid cap:@ %a."
        pp_value v
    | LblCallUnexpectedArgument v ->
      Format.fprintf fmt
        "Unexpected argument to labeled type projection:@ %a."
        pp_value v
    | UnexpectedEnvCell _ ->
      Format.fprintf fmt
        "Did not find what was expected in the environment."
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
    | UnleashDataError v ->
      Format.fprintf fmt
        "Tried to unleash %a as datatype."
        pp_value v
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
    | UnleashBoxModalityError v ->
      Format.fprintf fmt
        "Tried to unleash %a as box modality."
        pp_value v
    | UnleashExtError v ->
      Format.fprintf fmt
        "Tried to unleash %a as extension type."
        pp_value v
    | UnleashCoRError v ->
      Format.fprintf fmt
        "Tried to unleash %a as co-restriction type."
        pp_value v
    | UnleashFHComError v ->
      Format.fprintf fmt
        "Tried to unleash %a as formal homogeneous composition."
        pp_value v
    | UnleashLblTyError v ->
      Format.fprintf fmt
        "Tried to unleash %a as labeled type."
        pp_value v
    | ForcedUntrueCorestriction face ->
      Format.fprintf fmt
        "Cannot force untrue co-restriction:@ %a."
        pp_val_face face
    | ForcedUnexpectedCorestriction v ->
      Format.fprintf fmt
        "Cannot force unrecognized co-restriction:@ %a."
        pp_value v


  exception E = E

  let _ =
    PpExn.install_printer @@ fun fmt ->
    function
    | E err ->
      pp fmt err
    | _ ->
      raise PpExn.Unrecognized
end


module M (Sig : Sig) : S with module Sig = Sig =
struct
  module Sig = Sig

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
            | `Dim x -> x
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
            | `Tick tck -> tck
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

    | FHCom info ->
      make_fhcom
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

    | BoxModality v ->
      make @@ BoxModality (Value.act phi v)

    | Shut v ->
      make @@ Shut (Value.act phi v)

    | Data lbl ->
      make @@ Data lbl

    | Intro info ->
      begin
        match force_val_sys @@ ValSys.act phi @@ ValSys.from_rigid info.sys with
        | `Ok sys ->
          let args = List.map (Value.act phi) info.args in
          let rs = List.map (I.act phi) info.rs in
          make @@ Intro {info with args; rs; sys}
        | `Proj v ->
          v
      end

  and act_neu phi con =
    match con with
    | NHCom info ->
      let dir = Dir.act phi info.dir in
      let ty = Value.act phi info.ty in
      let sys = CompSys.act phi info.sys in
      let cap =
        match act_neu phi info.cap with
        | Ret neu ->
          reflect ty neu []
        | Step cap -> cap
      in
      step @@ make_hcom dir ty cap sys

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

    | Elim info ->
      let mot = Clo.act phi info.mot in
      let go (lbl, nclo) = lbl, NClo.act phi nclo in
      let clauses = List.map go info.clauses in
      begin
        match act_neu phi info.neu with
        | Ret neu ->
          ret @@ Elim {info with mot; neu; clauses}
        | Step v ->
          step @@ elim_data info.dlbl mot v clauses
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

    | Var {name; ushift; twin} ->
      let tty, tsys = Sig.lookup name twin in
      let rho' = {Env.emp with global = phi} in
      let vsys = eval_tm_sys rho' @@ Tm.map_tm_sys (Tm.shift_univ ushift) tsys in
      let vty = eval rho' @@ Tm.shift_univ ushift tty in
      step @@ reflect vty (Var {name; ushift; twin}) vsys

    | Meta {name; ushift} ->
      let tty, tsys = Sig.lookup name `Only in
      let rho' = {Env.emp with global = phi} in
      let vsys = eval_tm_sys rho' @@ Tm.map_tm_sys (Tm.shift_univ ushift) tsys in
      let vty = eval rho' @@ Tm.shift_univ ushift tty in
      step @@ reflect vty (Meta {name; ushift}) vsys

    | Prev (tick, neu) ->
      begin
        match act_neu phi neu with
        | Ret neu ->
          ret @@ Prev (tick, neu)
        | Step v ->
          step @@ prev tick v
      end

    | Open neu ->
      begin
        match act_neu phi neu with
        | Ret neu ->
          ret @@ Open neu
        | Step v ->
          step @@ modal_open v
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

  and unleash : value -> con =
    fun (Node info) ->
      let con =
        match info.action = I.idn with
        | true ->
          info.con
        | false ->
          let node' = act_can info.action info.con in
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

  and make_fhcom mdir cap msys : value =
    match mdir with
    | `Ok dir ->
      begin
        match msys with
        | `Ok sys ->
          rigid_fhcom dir cap sys
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
    | Pi _ | Sg _ | Ext _ | Up _ | Later _ | BoxModality _ ->
      make @@ Coe {dir; abs; el}

    | S1 | Univ _ ->
      el


    (* TODO: will need to change when indexed types are added *)
    | Data _ ->
      el

    | FHCom fhcom ->
      (* [F]: favonia 11.00100100001111110110101010001000100001011.
       * [SVO]: Part III (airport).
       * [R1]: RedPRL I ddcc4ce72b1880671d842ede6b50adbee94935b5.
       * [Y]: yacctt 073694948042342d55cea64a42d2076365800ee4. *)

      (* Some helper functions to reduce typos. *)
      let r, r' = Dir.unleash dir in
      let s, s' = Dir.unleash fhcom.dir in
      let cap_abs = Abs.bind1 x fhcom.cap in
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
          (Value.act (I.cmp phi subst_r) fhcom.cap)
          (make_cap
             (Dir.act (I.cmp phi subst_r) fhcom.dir)
             (Value.act (I.cmp phi subst_r) fhcom.cap)
             (CompSys.act (I.cmp phi subst_r) fhcom.sys)
             (Value.act phi el))
          (force_abs_sys @@ List.map (fun b -> face (AbsFace.act (I.cmp phi subst_r) b)) fhcom.sys)
      in
      (* This is N in [F, SVO], representing the coherence conditions enforced by `fhcom.sys`.
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
      (* This is P in [F, SVO], the naive coercion of the cap part of the box within `fhcom.cap`.
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
        diag @ List.map (fun b -> face (AbsFace.act phi b)) (CompSys.forall x fhcom.sys)
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
        diag :: List.map (fun b -> face (AbsFace.act phi b)) (CompSys.forall x fhcom.sys)
      in
      (* This is the "cap" part of the final request in [F, SVO].
       *
       * Using Q, the preimages, this is to calculate the final cap based on the naive cap. *)
      let coerced_cap =
        make_hcom (Dir.act subst_r' fhcom.dir) (Value.act subst_r' fhcom.cap) (naively_coerced_cap I.idn) @@
        force_abs_sys @@
        let diag = AbsFace.make_from_dir I.idn dir @@ fun phi ->
          Abs.make1 @@ fun w -> origin phi (`Atom w) in
        let face = Face.map @@ fun sj s'j absj ->
          let phi = I.equate sj s'j in
          Abs.make1 @@ fun w ->
          make_coe (Dir.make (`Atom w) (I.act phi (I.act subst_r' s))) absj @@
          recovery_general phi absj (`Atom w)
        in
        diag :: List.map (fun b -> face (AbsFace.act subst_r' b)) fhcom.sys
      in
      make_box (Dir.act subst_r' fhcom.dir) coerced_cap @@
      force_val_sys @@
      let face = Face.map @@ fun sj s'j absj ->
        let phi = I.equate sj s'j in
        recovery_general phi absj (I.act (I.cmp phi subst_r') s')
      in List.map (fun b -> face (AbsFace.act subst_r' b)) fhcom.sys


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
            eval (Env.push_many [`Val (Value.act phi ty00); `Val (Value.act phi ty10); `Val (car (Value.act phi equiv0)); `Val b] Env.emp) @@
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

  (* presupposes no dimension arguments *)
  and rigid_hcom_strict_data dir ty cap sys =
    match unleash ty, unleash cap with
    | Data dlbl, Intro info ->
      let peel_arg k el =
        match unleash el with
        | Intro info' ->
          List.nth info'.args k
        | _ ->
          failwith "rigid_hcom_strict_data: peel_arg"
      in

      let peel_face k =
        Face.map @@ fun _ _ abs ->
        let x, elx = Abs.unleash1 abs in
        Abs.bind1 x @@ peel_arg k elx
      in

      let peel_sys k sys = List.map (peel_face k) sys in

      let rec make_args i acc args ps atys =
        match args, ps, atys with
        | el :: args, _ :: ps, _ ->
          make_args (i + 1) (acc #< el) args ps atys
        | el :: args, [], (_, Desc.Self) :: atys ->
          let hcom = rigid_hcom dir ty el (peel_sys i sys) in
          make_args (i + 1) (acc #< hcom) args ps atys
        | [], [], [] ->
          Bwd.to_list acc
        | _ ->
          failwith "rigid_hcom_strict_data"
      in

      let desc = Sig.lookup_datatype dlbl in
      let constr = Desc.lookup_constr info.clbl desc in

      let args' = make_args 0 Emp info.args constr.params constr.args in

      make @@ Intro {dlbl; clbl = info.clbl; args = args'; rs = []; sys = []}

    | _, Up info ->
      rigid_nhcom_up dir info.ty info.neu ~comp_sys:sys ~rst_sys:info.sys

    | _ ->
      raise @@ E (RigidHComUnexpectedArgument cap)


  and rigid_nhcom_up dir ty cap ~comp_sys ~rst_sys =
    let neu = NHCom {dir; ty; cap; sys = comp_sys} in
    let hcom_face r r' el =
      let phi = I.equate r r' in
      let dir_phi = Dir.act phi dir in
      let ty_phi = Value.act phi ty in
      let sys_phi = CompSys.act phi comp_sys in
      make_hcom dir_phi ty_phi el sys_phi
    in
    let rst_sys = List.map (Face.map hcom_face) rst_sys in
    make @@ Up { ty; neu; sys = rst_sys}

  and rigid_hcom dir ty cap sys : value =
    match unleash ty with
    | Pi _ | Sg _ | Ext _ | Up _ ->
      make @@ HCom {dir; ty; cap; sys}

    | S1 ->
      make @@ FHCom {dir; cap; sys}

    | Data dlbl ->
      let desc = Sig.lookup_datatype dlbl in
      if Desc.is_strict_set desc then
        rigid_hcom_strict_data dir ty cap sys
      else
        make @@ FHCom {dir; cap; sys}

    | Univ _ ->
      rigid_fhcom dir cap sys

    | FHCom fhcom ->
      (* [F]: favonia 11.00100100001111110110101010001000100001011.
       * [SVO]: Part III (airport).
       * [R1]: RedPRL I ddcc4ce72b1880671d842ede6b50adbee94935b5.
       * [Y]: yacctt 073694948042342d55cea64a42d2076365800ee4. *)

      (* The algorithm is based on the Anders' alternative hcom in [F]. *)

      (* Helper functions. *)
      let r, r' = Dir.unleash dir in
      let _, s' = Dir.unleash fhcom.dir in

      (* This is C_M in [F], with an extra parameter `phi` to get along with NbE. *)
      let cap_aux phi el = make_cap (Dir.act phi fhcom.dir) (Value.act phi fhcom.cap) (CompSys.act phi fhcom.sys) el in

      (* This serves as `O` and the diagonal face in [F]
       * for the coherence conditions in `fhcom.sys` and `s=s'`. *)
      let hcom_template phi y_dest ty = make_hcom
          (Dir.make (I.act phi r) y_dest) ty
          (Value.act phi fhcom.cap) (CompSys.act phi fhcom.sys)
      in

      (* This is `P` in [F]. *)
      let new_cap = rigid_hcom dir fhcom.cap (cap_aux I.idn cap) @@
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
          List.map face fhcom.sys
        in
        let diag = AbsFace.make_from_dir I.idn fhcom.dir @@ fun phi ->
          Abs.make1 @@ fun y -> hcom_template phi (`Atom y) (Value.act phi fhcom.cap)
        in
        Option.filter_map force_abs_face [diag] @ (ri_faces @ si_faces)
      in
      let boundary = Face.map @@ fun si s'i abs ->
        let phi = I.equate si s'i in
        hcom_template phi (I.act phi r') (Value.act phi (Abs.inst1 abs s'))
      in
      rigid_box fhcom.dir new_cap
        (List.map boundary fhcom.sys)

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
            let yi, el = Abs.unleash absi in
            Abs.bind yi @@ vproj phi (I.act phi @@ `Atom x) ~ty0:(fun phi -> Value.act phi ty0) ~ty1:ty1 ~equiv:(fun phi -> Value.act phi equiv) ~el
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
    | Pi _ | Sg _ | Up _ ->
      make @@ GHCom {dir; ty; cap; sys}

    (* `Ext _`: the expansion will stop after a valid
     * correction system, so it is not so bad. *)
    | Ext _ | Univ _ | FHCom _ | V _ | S1 | Data _ ->
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

  and rigid_fhcom dir cap sys : value =
    make @@ FHCom {dir; cap; sys}

  and rigid_box dir cap sys : value =
    make @@ Box {dir; cap; sys}


  and clo bnd rho =
    Clo {bnd; rho}

  and nclo nbnd rho =
    NClo {nbnd; rho}

  and eval_bterm dlbl desc (rho : env) btm =
    match btm with
    | B.Intro info ->
      let constr = Desc.lookup_constr info.clbl desc in
      let const_args = List.map (eval rho) info.const_args in
      let rec_args = List.map (eval_bterm dlbl desc rho) info.rec_args in
      let rs = List.map (eval_dim rho) info.rs in
      let sys = eval_bterm_boundary dlbl desc rho constr.boundary const_args rec_args rs in
      begin
        match force_val_sys sys with
        | `Proj v ->
          v
        | `Ok sys ->
          make @@ Intro {dlbl; clbl = info.clbl; args = const_args @ rec_args; rs; sys}
      end

    | B.Var ix ->
      begin
        match List.nth rho.cells ix with
        | `Val v -> v
        | cell ->
          let err = UnexpectedEnvCell cell in
          raise @@ E err
      end

  and eval_bterm_boundary dlbl desc rho sys const_args rec_args rs =
    List.map (eval_bterm_face dlbl desc rho const_args rec_args rs) sys

  and eval_bterm_face dlbl desc rho const_args rec_args rs (tr0, tr1, btm) =
    let rho' =
      Env.push_many
        begin
          List.map (fun x -> `Val x) const_args
          @ List.map (fun x -> `Val x) rec_args
          @ List.map (fun x -> `Dim x) rs
        end
        rho
    in
    let r0 = eval_dim rho' tr0 in
    let r1 = eval_dim rho' tr1 in
    match Eq.make r0 r1 with
    | `Ok xi ->
      let v = Value.act (I.equate r0 r1) @@ eval_bterm dlbl desc rho' btm in
      Face.Indet (xi, v)
    | `Apart _ ->
      Face.False (r0, r1)
    | `Same _ ->
      let v = eval_bterm dlbl desc rho' btm in
      Face.True (r0, r1, v)


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

    | Tm.FHCom info ->
      let r = eval_dim rho info.r  in
      let r' = eval_dim rho info.r' in
      let dir = Dir.make r r' in
      let cap = eval rho info.cap in
      let sys = eval_rigid_bnd_sys rho info.sys in
      make_fhcom dir cap sys

    | Tm.Univ {kind; lvl} ->
      make @@ Univ {kind; lvl}

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
      eval (Env.push (`Val v0) rho) t

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

    | Tm.BoxModality ty ->
      let vty = eval rho ty in
      make @@ BoxModality vty

    | Tm.Shut t ->
      let v = eval rho t in
      make @@ Shut v

    | Tm.Data lbl ->
      make @@ Data lbl

    | Tm.Intro (dlbl, clbl, args) ->
      let desc = Sig.lookup_datatype dlbl in
      let constr = Desc.lookup_constr clbl desc in
      let args, trs = ListUtil.split (List.length constr.params + List.length constr.args) args in
      let vargs = List.map (eval rho) args in
      let rs = List.map (eval_dim rho) trs in
      make_intro (Env.clear_locals rho) ~dlbl ~clbl ~args:vargs ~rs


  and make_intro rho ~dlbl ~clbl ~args ~rs =
    let desc = Sig.lookup_datatype dlbl in
    let constr = Desc.lookup_constr clbl desc in
    let const_args, rec_args = ListUtil.split (List.length constr.params) args in
    let sys = eval_bterm_boundary dlbl desc rho constr.boundary const_args rec_args rs in
    match force_val_sys sys with
    | `Ok sys ->
      make @@ Intro {dlbl; clbl; args; rs; sys}
    | `Proj v ->
      v

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
    | Tm.Open ->
      modal_open vhd
    | Tm.Elim info ->
      let mot = clo info.mot rho in
      let clauses = List.map (fun (lbl, nbnd) -> lbl, nclo nbnd rho) info.clauses in
      elim_data info.dlbl mot vhd clauses


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
        | `Val v -> v
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
    let rho = Env.push (`Dim (`Atom x)) rho in
    Abs.bind1 x @@ eval rho tm

  and eval_nbnd rho bnd =
    let Tm.NB (nms, tm) = bnd in
    let xs = Bwd.map Name.named nms in
    let rho = Env.push_many (List.rev @@ Bwd.to_list @@ Bwd.map (fun x -> `Dim (`Atom x)) xs) rho in
    Abs.bind xs @@ eval rho tm

  and eval_ext_bnd rho bnd =
    let Tm.NB (nms, (tm, sys)) = bnd in
    let xs = Bwd.map Name.named nms in
    let rho = Env.push_many (List.rev @@ Bwd.to_list @@ Bwd.map (fun x -> `Dim (`Atom x)) xs) rho in
    ExtAbs.bind xs (eval rho tm, eval_tm_sys rho sys)

  and unleash_data v =
    match unleash v with
    | Data dlbl -> dlbl
    | Rst rst -> unleash_data rst.ty
    | _ ->
      raise @@ E (UnleashDataError v)

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

  and unleash_box_modality v =
    match unleash v with
    | BoxModality ty -> ty
    | Rst rst -> unleash_box_modality rst.ty
    | _ ->
      raise @@ E (UnleashBoxModalityError v)

  and unleash_sg v =
    match unleash v with
    | Sg {dom; cod} -> dom, cod
    | Rst rst -> unleash_sg rst.ty
    | _ ->
      raise @@ E (UnleashSgError v)

  and unleash_ext_with v rs =
    match unleash v with
    | Ext abs ->
      ExtAbs.inst abs (Bwd.from_list rs)
    | Rst rst ->
      unleash_ext_with rst.ty rs
    | _ ->
      raise @@ E (UnleashExtError v)

  and unleash_ext v =
    match unleash v with
    | Ext abs ->
      abs
    | Rst rst ->
      unleash_ext rst.ty
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

  and unleash_fhcom v =
    match unleash v with
    | FHCom info -> info.dir, info.cap, info.sys
    | Rst rst -> unleash_fhcom rst.ty
    | _ ->
      raise @@ E (UnleashFHComError v)

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
      raise @@ E (ForcedUnexpectedCorestriction v)

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
      raise @@ E (ApplyUnexpectedFunction vfun)

  and ext_apply vext (ss : I.t list) =
    match unleash vext with
    | ExtLam abs ->
      Abs.inst abs (Bwd.from_list ss)

    | Up info ->
      let tyr, sysr = unleash_ext_with info.ty ss in
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
      let ty_s, sys_s = unleash_ext_with ext_y ss in
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
      let ty_s, sys_s = unleash_ext_with info.ty ss in
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
      raise @@ E (ApplyUnexpectedCube vext)

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


  and modal_open el =
    match unleash el with
    | Shut el ->
      el

    | Up info ->
      let ty = unleash_box_modality info.ty in
      let open_face = Face.map @@ fun _ _ a -> modal_open a in
      let open_sys = List.map open_face info.sys in
      make @@ Up {ty; neu = Open info.neu; sys = open_sys}

    | Coe info ->
      (* EXPERIMENTAL !!! *)
      let x, boxtyx = Abs.unleash1 info.abs in
      let tyx = unleash_box_modality boxtyx in
      let abs = Abs.bind1 x tyx in
      let el = modal_open info.el in
      rigid_coe info.dir abs el

    | HCom info ->
      (* EXPERIMENTAL !!! *)
      let ty = unleash_box_modality info.ty in
      let cap = modal_open info.cap in
      let open_face =
        Face.map @@ fun _ _ abs ->
        let x, v = Abs.unleash1 abs in
        Abs.bind1 x @@ modal_open v
      in
      let sys = List.map open_face info.sys in
      rigid_hcom info.dir ty cap sys

    | GHCom info ->
      (* EXPERIMENTAL !!! *)
      let ty = unleash_box_modality info.ty in
      let cap = modal_open info.cap in
      let open_face =
        Face.map @@ fun _ _ abs ->
        let x, v = Abs.unleash1 abs in
        Abs.bind1 x @@ modal_open v
      in
      let sys = List.map open_face info.sys in
      rigid_ghcom info.dir ty cap sys

    | _ ->
      failwith "modal_open"


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
      let err = RigidVProjUnexpectedArgument el in
      raise @@ E err

  and elim_data dlbl mot scrut clauses =
    match unleash scrut with
    | Intro info ->
      let _, nclo = List.find (fun (clbl', _) -> info.clbl = clbl') clauses in
      let desc = Sig.lookup_datatype dlbl in
      let constr = Desc.lookup_constr info.clbl desc in

      let rec go vs rs ps args dims =
        match vs, rs, ps, args, dims with
        | v :: vs, _, (_, _) :: ps, _, _ ->
          `Val v :: go vs rs ps args dims
        | v :: vs, _,  [], (_, Desc.Self) :: args, _ ->
          let v_ih = elim_data dlbl mot v clauses in
          `Val v :: `Val v_ih :: go vs rs [] args dims
        | [], r :: rs, [], [], _ :: dims ->
          `Dim r :: go [] rs [] [] dims
        | [], [], [], [], [] ->
          []
        | _ ->
          failwith "elim_data/intro"
      in

      inst_nclo nclo @@ go info.args info.rs constr.params constr.args constr.dims

    | Up up ->
      let neu = Elim {dlbl; mot; neu = up.neu; clauses} in
      let mot' = inst_clo mot scrut in
      let elim_face =
        Face.map @@ fun r r' a ->
        let phi = I.equate r r' in
        let clauses' = List.map (fun (lbl, nclo) -> lbl, NClo.act phi nclo) clauses in
        elim_data dlbl (Clo.act phi mot) a clauses'
      in
      let elim_sys = List.map elim_face up.sys in
      make @@ Up {ty = mot'; neu; sys = elim_sys}

    | _ ->
      raise @@ E (RecursorUnexpectedArgument ("data type", scrut))

  and s1_rec mot scrut bcase lcase =
    match unleash scrut with
    | Base ->
      bcase
    | Loop x ->
      Abs.inst1 lcase @@ `Atom x
    | FHCom info ->
      let apply_rec tm = s1_rec mot tm bcase lcase in
      let r, _ = Dir.unleash info.dir in
      let ty = Abs.make1 @@ fun y ->
        inst_clo mot @@
        make_fhcom (Dir.make r (`Atom y)) info.cap (`Ok info.sys)
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
      raise @@ E (RecursorUnexpectedArgument ("the circle", scrut))

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
      raise @@ E (SigmaProjUnexpectedArgument ("car", v))

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
      raise @@ E (SigmaProjUnexpectedArgument ("cdr", v))

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
      raise @@ E (RigidCapUnexpectedArgument el)


  and inst_clo clo varg =
    match clo with
    | Clo info ->
      let Tm.B (_, tm) = info.bnd in
      eval (Env.push (`Val varg) info.rho) tm

  and inst_nclo nclo vargs =
    match nclo with
    | NClo info ->
      let Tm.NB (_, tm) = info.nbnd in
      (* Reversing makes sense here because: the left-most element of the environment is the innermost variable *)
      eval (Env.push_many (List.rev vargs) info.rho) tm

  and inst_tick_clo clo tick =
    match clo with
    | TickClo info ->
      let Tm.B (_, tm) = info.bnd in
      eval (Env.push (`Tick tick) info.rho) tm
    | TickCloConst v ->
      v

  module Macro =
  struct
    let equiv ty0 ty1 : value =
      let rho = Env.push_many [`Val ty0; `Val ty1] Env.emp in
      eval rho @@
      Tm.Macro.equiv
        (Tm.up @@ Tm.ix 0)
        (Tm.up @@ Tm.ix 1)

  end

end

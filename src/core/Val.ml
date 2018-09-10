open RedBasis
open Bwd
open BwdNotation
open Domain

include ValSig

let flip f x y = f y x

exception StrictHComEncounteredNonConstructor


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
  | UnleashRestrictError of value
  | UnleashLblTyError of value
  | UnleashFHComError of value
  | ForcedUntrueRestriction of val_face
  | ForcedUnexpectedRestriction of value


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
    | UnexpectedEnvCell cell ->
      Format.fprintf fmt
        "Did not find what was expected in the environment: %a"
        pp_env_cell cell
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
    | UnleashExtError v ->
      Format.fprintf fmt
        "Tried to unleash %a as extension type."
        pp_value v
    | UnleashRestrictError v ->
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
    | ForcedUntrueRestriction face ->
      Format.fprintf fmt
        "Cannot force untrue co-restriction:@ %a."
        pp_val_face face
    | ForcedUnexpectedRestriction v ->
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

  let empty_env = Env.emp Sig.global_dims

  let make_closure rho bnd =
    Clo {bnd; rho}

  let rec eval_dim rho tm =
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
            match Bwd.nth rho.cells i with
            | `Dim x -> x
            | cell ->
              let err = UnexpectedEnvCell cell in
              raise @@ E err
          end

        | Tm.Var info ->
          begin
            match DimEnv.find_opt info.name rho.global with
            | Some r -> r
            | None -> `Atom info.name
          end

        | Tm.DownX r ->
          eval_dim rho r

        | _ ->
          let err = ExpectedDimensionTerm tm in
          raise @@ E err
      end
    | _ ->
      let err = ExpectedDimensionTerm tm in
      raise @@ E err

  let eval_tick rho tm =
    match Tm.unleash tm with
    | Tm.Up (hd, Emp) ->
      begin
        match hd with
        | Tm.Ix (i, _) ->
          begin
            match Bwd.nth rho.cells i with
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

    | Restrict face ->
      let face = ValFace.act phi face in
      make @@ Restrict face

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

    | Lam clo ->
      make @@ Lam (Clo.act phi clo)

    | ExtLam clo ->
      make @@ ExtLam (NClo.act phi clo)

    | RestrictThunk v ->
      make @@ RestrictThunk (ValFace.act phi v)

    | Cons (v0, v1) ->
      make @@ Cons (Value.act phi v0, Value.act phi v1)

    | LblTy {lbl; ty; args} ->
      make @@ LblTy {lbl; ty = Value.act phi ty; args = List.map (Nf.act phi) args}

    | LblRet v ->
      make @@ LblRet (Value.act phi v)

    | Up info ->
      let sys = ValSys.act phi @@ ValSys.from_rigid info.sys in
      begin
        match force_val_sys sys with
        | `Proj v -> v
        | `Ok sys ->
          let ty = Value.act phi info.ty in
          let neu = Neu.act phi info.neu in
          make @@ Up {ty; neu; sys}
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

    | Data lbl ->
      make @@ Data lbl

    | Intro info ->
      begin
        match force_val_sys @@ ValSys.act phi @@ ValSys.from_rigid info.sys with
        | `Ok sys ->
          let const_args = List.map (Value.act phi) info.const_args in
          let rec_args = List.map (Value.act phi) info.rec_args in
          let rs = List.map (I.act phi) info.rs in
          make @@ Intro {info with const_args; rec_args; rs; sys}
        | `Proj v ->
          v
      end

  and unleash : value -> con =
    fun (Node info) ->
      match info.action = I.idn with
      | true ->
        info.con
      | false ->
        let node' = act_can info.action info.con in
        let con = unleash node' in
        con

  and make_cons (a, b) = make @@ Cons (a, b)
  and make_dfix_line r ty clo =
    match r with
    | `Atom x ->
      make @@ DFixLine {x; ty; clo}
    | `Dim0 ->
      make @@ DFix {ty; clo}
    | `Dim1 ->
      let bdy = lazy begin inst_clo clo @@ make @@ DFix {ty; clo} end in
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

  and rigid_ncoe_up dir abs neu ~rst_sys =
    let ncoe = NCoe {dir; abs; neu} in
    let r, r' = Dir.unleash dir in
    let ty = Abs.inst1 abs r' in
    let coe_face s s' el =
      let phi = I.equate s s' in
      let dir_phi = Dir.act phi dir in
      let abs_phi = Abs.act phi abs in
      make_coe dir_phi abs_phi el
    in

    let rr'_face =
      match Eq.from_dir dir with
      | `Ok xi ->
        let el =
          lazy begin
            let phi = I.equate r r' in
            match force_val_sys @@ ValSys.act phi @@ ValSys.from_rigid rst_sys with
            | `Proj v ->
              v
            | `Ok sys ->
              let neu' = Neu.act phi neu in
              make @@ Up {ty = Value.act phi ty; neu = neu'; sys}
          end
        in
        [Face.Indet (xi, el)]
      | `Apart _ ->
        []
    in

    let ncoe_sys = rr'_face @ List.map (Face.map coe_face) rst_sys in
    make @@ Up {ty; neu = ncoe; sys = ncoe_sys}

  (* TODO: check that this is right *)
  and rigid_multi_coe env dir (x, const_specs) args =
    match const_specs, args with
    | [], [] ->
      []
    | (_, spec) :: const_specs, arg :: args ->
      let vty = eval env spec in
      let r, r' = Dir.unleash dir in
      let coe_hd s = make_coe (Dir.make r s) (Abs.bind1 x vty) arg in
      let coe_tl =
        let coe_hd_x = coe_hd @@ `Atom x in
        rigid_multi_coe (Env.snoc env @@ `Val coe_hd_x) dir (x, const_specs) args
      in
      coe_hd r' :: coe_tl
    | _ ->
      failwith "rigid_multi_coe: length mismatch"

  and multi_coe env mdir (x, const_specs) args =
    match mdir with
    | `Ok dir ->
      rigid_multi_coe env dir (x, const_specs) args
    | `Same _ ->
      args

  (* Figure 8 of Part IV: https://arxiv.org/abs/1801.01568v3; specialized to non-indexed HITs. *)
  and rigid_coe_nonstrict_data_intro dir abs ~dlbl ~clbl ~const_args ~rec_args ~rs =
    let x = Name.fresh () in
    let desc = Sig.lookup_datatype dlbl in
    let constr = Desc.lookup_constr clbl desc in

    let r, r' = Dir.unleash dir in

    let make_const_args dir =
      multi_coe empty_env dir (x, constr.const_specs) const_args
    in

    let coe_rec_arg dir _arg_spec arg =
      (* TODO: when we add more recursive argument types, please fix!!! Change this to coerce in the
         realization of the "argument spec". *)
      make_coe dir abs arg
    in

    let make_rec_args dir = List.map2 (coe_rec_arg dir) constr.rec_specs rec_args in
    let intro =
      make_intro empty_env ~dlbl ~clbl
        ~const_args:(make_const_args (`Ok dir))
        ~rec_args:(make_rec_args (`Ok dir))
        ~rs
    in

    begin
      match constr.boundary with
      | [] ->
        intro
      | _ ->
        (* My lord, I have no idea if this is right. ouch!! *)
        let faces =
          eval_bterm_boundary dlbl desc empty_env
            ~const_args:(make_const_args @@ Dir.make r (`Atom x))
            ~rec_args:(make_rec_args @@ Dir.make r (`Atom x))
            ~rs
            constr.boundary
        in
        let fix_face =
          Face.map @@ fun _ _ el ->
          Abs.bind1 x @@ make_coe (Dir.make (`Atom x) r') abs el
        in
        let correction = List.map fix_face faces in
        make_fhcom (`Ok (Dir.swap dir)) intro @@ force_abs_sys correction
    end

  and rigid_coe_nonstrict_data dir abs el =
    let _, tyx = Abs.unsafe_unleash abs in
    match unleash tyx, unleash el with
    | Data dlbl, Intro info ->
      rigid_coe_nonstrict_data_intro dir abs ~dlbl ~clbl:info.clbl ~const_args:info.const_args ~rec_args:info.rec_args ~rs:info.rs

    | Data _, Up info ->
      rigid_ncoe_up dir abs info.neu ~rst_sys:info.sys

    | Data _, FHCom info ->
      let cap = rigid_coe dir abs info.cap in
      let face =
        Face.map @@ fun r r' abs' ->
        let y, v = Abs.unleash1 abs' in
        let phi = I.equate r r' in
        Abs.bind1 y @@ make_coe (Dir.act phi dir) (Abs.act phi abs) v
      in
      let sys = List.map face info.sys in
      rigid_fhcom info.dir cap sys

    | _ ->
      failwith "rigid_coe_nonstrict_data"

  and rigid_coe dir abs el =
    let x, tyx = Abs.unleash1 abs in
    match unleash tyx with
    | Pi _ | Sg _ | Ext _ | Later _ ->
      make @@ Coe {dir; abs; el}

    | Up info ->
      let abs = NeuAbs.bind1 x (info.neu, ValSys.from_rigid info.sys) in
      let neu = NCoeAtType {dir; abs; el} in
      let r, r' = Dir.unleash dir in
      let ty_r' =
        let univ = make @@ Univ {lvl = `Omega; kind = `Pre} in
        let neu_ty_r', neu_sys_r' = NeuAbs.inst1 abs r' in
        reflect univ neu_ty_r' neu_sys_r'
      in
      let sys_rr' =
        match Eq.from_dir dir with
        | `Ok xi ->
          [Face.Indet (xi, lazy begin Value.act (I.equate r r') el end)]
        | `Apart _ ->
          []
      in
      let sys =
        let face =
          Face.map @@ fun s s' v ->
          let phi = I.equate s s' in
          let abs = Abs.bind1 x v in
          make_coe (Dir.act phi dir) abs (Value.act phi el)
        in
        sys_rr' @ List.map face @@ ValSys.forall x @@ ValSys.from_rigid info.sys
      in
      reflect ty_r' neu sys

    (* TODO: what about neutral element of the universe? is this even correct? *)
    | Univ _ ->
      el

    | Data dlbl ->
      let desc = Sig.lookup_datatype dlbl in
      if Desc.is_strict_set desc then el
      (* for data types without parameters, coe can be the identity *)
      else el (*rigid_coe_nonstrict_data dir abs el*)

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
        make_coe (Dir.make (I.act (I.cmp subst_x phi) s') (I.act subst_x z_dest)) (Abs.act subst_x abs) @@
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
        let diag =
          AbsFace.make phi (I.act phi r) (I.act phi r') @@ fun phi ->
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
        let diag =
          AbsFace.make_from_dir I.idn dir @@ fun phi ->
          Abs.make1 @@ fun w -> origin phi (`Atom w) in
        let face =
          Face.map @@ fun sj s'j absj ->
          let phi = I.equate sj s'j in
          Abs.make1 @@ fun w ->
          make_coe (Dir.make (`Atom w) (I.act phi (I.act subst_r' s))) absj @@
          recovery_general phi absj (`Atom w)
        in
        diag :: List.map (fun b -> face (AbsFace.act subst_r' b)) fhcom.sys
      in
      make_box (Dir.act subst_r' fhcom.dir) coerced_cap @@
      force_val_sys @@
      let face =
        Face.map @@ fun sj s'j absj ->
        let phi = I.equate sj s'j in
        recovery_general phi absj (I.act (I.cmp phi subst_r') s')
      in
      List.map (fun b -> face (AbsFace.act subst_r' b)) fhcom.sys


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
              ~func:(fun phi0 -> Value.act phi0 @@ subst_src @@ car info.equiv)
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
          let face_diag =
            AbsFace.make_from_dir I.idn dir @@ fun phi ->
            Abs.make1 @@ fun _ -> base phi (I.act phi r) (I.act phi r')
          in
          (* The face for r=0. *)
          let face0 =
            AbsFace.make I.idn r `Dim0 @@ fun phi ->
            Abs.make1 @@ fun _ -> base0 phi (I.act phi r')
          in
          (* The face for r=1. This more optimized version is used
           * in [Y], [F] and [R1] but not [SVO]. *)
          let face1 =
            AbsFace.make I.idn r `Dim1 @@ fun phi ->
            Abs.make1 @@ fun y ->
            let ty = Value.act phi @@ subst_r' info.ty1 in
            let cap = base1 phi (I.act phi r') in
            let msys = force_abs_sys @@
              let face0 =
                AbsFace.make phi (I.act phi r') `Dim0 @@ fun phi ->
                Abs.make1 @@ fun z -> ext_apply (cdr (fiber0 phi cap)) [`Atom z]
              in
              let face1 =
                AbsFace.make phi (I.act phi r') `Dim1 @@ fun phi ->
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
            let env = Env.append empty_env [`Val b; `Val (car (Value.act phi equiv0)); `Val (Value.act phi ty10); `Val (Value.act phi ty00)] in
            eval env @@ Tm.fiber ~ty0:(var 0) ~ty1:(var 1) ~f:(var 2) ~x:(var 3)
          in
          (* This is to generate the element in `ty0` and also
           * the face for r'=0. This is `O` in [F]. *)
          let fixer_fiber phi =
            (* Turns out `fiber_at_face0` will be
             * used for multiple times. *)
            let fiber_at_face0 phi =
              make_cons
                (Value.act phi el,
                 make @@ ExtLam (NCloConst (lazy begin base0 phi `Dim0 end)))
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
                    make_cons
                      (Value.act (I.cmp phi (I.subst `Dim0 r_atom)) el,
                       make @@ ExtLam (NCloConst (lazy begin base0 phi `Dim0 end)))
                  in
                  ext_apply path_in_fiber0_ty [r]
              end
            (* The implementation used in [Y]. *)
            | `UNIFORM_HCOM ->
              (* hcom whore cap is (fiber0 base), r=0 face is contr0, and r=1 face is constant *)
              make_hcom (Dir.make `Dim1 `Dim0) (fiber0_ty phi (base phi (I.act phi r) `Dim0)) (fiber0 phi (base phi (I.act phi r) `Dim0)) @@
              force_abs_sys @@
              let face0 =
                AbsFace.make phi (I.act phi r) `Dim0 @@ fun phi ->
                Abs.make1 @@ fun w -> ext_apply (contr0 phi (fiber_at_face0 phi)) [`Atom w]
              in
              let face1 =
                AbsFace.make phi (I.act phi r) `Dim1 @@ fun phi ->
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
              let funcr = Value.act phi @@ car info.equiv in
              rigid_vproj info.x ~func:funcr ~el
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
          List.nth (info'.const_args @ info'.rec_args) k
        | Up _ ->
          raise StrictHComEncounteredNonConstructor
        | _ ->
          Format.eprintf "Very bad: %a@." pp_value el;
          failwith "rigid_hcom_strict_data: peel_arg"
      in

      let peel_face k =
        Face.map @@ fun _ _ ->
        Abs.unsafe_map (peel_arg k)
      in

      let peel_sys k sys = List.map (peel_face k) sys in

      let rec make_args i acc cvs rvs const_specs rec_specs =
        match cvs, rvs, const_specs, rec_specs with
        | el :: cvs, _, _ :: const_specs, _ ->
          make_args (i + 1) (acc #< el) cvs rvs const_specs rec_specs
        | [], el :: rvs, [], (_, Desc.Self) :: rec_specs ->
          let hcom = rigid_hcom dir ty el (peel_sys i sys) in
          make_args (i + 1) (acc #< hcom) cvs rvs const_specs rec_specs
        | [], [], [], []->
          Bwd.to_list acc
        | _ ->
          failwith "rigid_hcom_strict_data"
      in

      let desc = Sig.lookup_datatype dlbl in
      let constr = Desc.lookup_constr info.clbl desc in

      let args' = make_args 0 Emp info.const_args info.rec_args constr.const_specs constr.rec_specs in
      let const_args, rec_args = ListUtil.split (List.length constr.const_specs) args' in

      make @@ Intro {dlbl; clbl = info.clbl; const_args; rec_args; rs = []; sys = []}

    | _, Up info ->
      rigid_nhcom_up_at_cap dir info.ty info.neu ~comp_sys:sys ~rst_sys:info.sys

    | _ ->
      raise @@ E (RigidHComUnexpectedArgument cap)


  and rigid_nhcom_up_at_type dir univ ty cap ~comp_sys ~rst_sys =
    let neu = NHComAtType {dir; univ; ty; cap; sys = comp_sys} in
    let hcom_face r r' ty =
      let phi = I.equate r r' in
      let dir_phi = Dir.act phi dir in
      let cap_phi = Value.act phi cap in
      let sys_phi = CompSys.act phi comp_sys in
      make_hcom dir_phi ty cap_phi sys_phi
    in
    let ty = reflect univ ty @@ ValSys.from_rigid rst_sys in
    let r, r' = Dir.unleash dir in
    let tube_face : ([`Rigid], _) face -> _ face =
      function
      | Face.Indet (xi, abs) ->
        let s, s' = Eq.unleash xi in
        let phi = I.equate s s' in
        Face.Indet (xi, lazy begin Abs.inst1 (Lazy.force abs) r' end)
    in
    let tube_faces = List.map tube_face comp_sys in
    let cap_face =
      match Eq.from_dir dir with
      | `Ok xi ->
        [Face.Indet (xi, lazy begin Value.act (I.equate r r') cap end)]
      | `Apart _ ->
        []
    in
    let rst_sys = cap_face @ tube_faces @ List.map (Face.map hcom_face) rst_sys in
    make @@ Up {ty; neu; sys = rst_sys}

  and rigid_nhcom_up_at_cap dir ty cap ~comp_sys ~rst_sys =
    let neu = NHComAtCap {dir; ty; cap; sys = comp_sys} in
    let hcom_face r r' el =
      let phi = I.equate r r' in
      let dir_phi = Dir.act phi dir in
      let ty_phi = Value.act phi ty in
      let sys_phi = CompSys.act phi comp_sys in
      make_hcom dir_phi ty_phi el sys_phi
    in
    let r, r' = Dir.unleash dir in
    let tube_face : ([`Rigid], _) face -> _ face =
      function
      | Face.Indet (xi, abs) ->
        let s, s' = Eq.unleash xi in
        let phi = I.equate s s' in
        Face.Indet (xi, lazy begin Abs.inst1 (Lazy.force abs) r' end)
    in
    let tube_faces = List.map tube_face comp_sys in
    let cap_face =
      match Eq.from_dir dir with
      | `Ok xi ->
        let phi = I.equate r r' in
        let el =
          lazy begin
            match force_val_sys @@ ValSys.act phi @@ ValSys.from_rigid rst_sys with
            | `Proj v -> v
            | `Ok sys ->
              make @@ Up {ty = Value.act phi ty; neu = Neu.act phi cap; sys}
          end
        in
        [Face.Indet (xi, el)]
      | `Apart _ ->
        []
    in
    let rst_sys = cap_face @ tube_faces @ List.map (Face.map hcom_face) rst_sys in
    make @@ Up {ty; neu; sys = rst_sys}

  and rigid_hcom dir ty cap sys : value =
    match unleash ty with
    | Pi _ | Sg _ | Ext _ ->
      make @@ HCom {dir; ty; cap; sys}

    | Up info ->
      rigid_nhcom_up_at_type dir info.ty info.neu cap ~comp_sys:sys ~rst_sys:info.sys

    | Data dlbl ->
      (* It's too expensive to determine in advance if the system has constructors in all faces, so we just disable strict composition for now. *)
      make @@ FHCom {dir; cap; sys}

    (* Note, that the following code looks like it would work, but it doesn't. The problem is that the exception gets thrown in a recursive call that is underneath a thunk,
       so it is never caught. Generally, backtracking is not something we would support during evaluation. *)

    (* let desc = Sig.lookup_datatype dlbl in
       if Desc.is_strict_set desc then
       try rigid_hcom_strict_data dir ty cap sys
       with
       | StrictHComEncounteredNonConstructor ->
        make @@ FHCom {dir; cap; sys}
       else
       make @@ FHCom {dir; cap; sys} *)

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
      let cap_aux phi el =
        let mdir = Dir.act phi fhcom.dir in
        let ty = Value.act phi fhcom.cap in
        let msys = CompSys.act phi fhcom.sys in
        make_cap mdir ty msys el
      in

      (* This serves as `O` and the diagonal face in [F]
       * for the coherence conditions in `fhcom.sys` and `s=s'`. *)
      let hcom_template phi y_dest ty =
        make_hcom
          (Dir.make (I.act phi r) y_dest)
          ty
          (Value.act phi cap)
          (CompSys.act phi sys)
      in

      (* This is `P` in [F]. *)
      let new_cap =
        rigid_hcom dir fhcom.cap (cap_aux I.idn cap) @@
        let ri_faces =
          let face =
            Face.map @@ fun ri r'i abs ->
            let y, el = Abs.unleash1 abs in
            Abs.bind1 y @@ cap_aux (I.equate ri r'i) el
          in
          List.map face sys
        in
        let si_faces =
          let face =
            Face.map @@ fun si s'i abs ->
            let phi = I.equate si s'i in
            Abs.make1 @@ fun y ->
            (* this is not the most efficient code, but maybe we can afford this? *)
            cap_aux phi @@ hcom_template phi (`Atom y) (Value.act phi (Abs.inst1 abs s'))
          in
          List.map face fhcom.sys
        in
        let diag =
          AbsFace.make_from_dir I.idn fhcom.dir @@ fun phi ->
          Abs.make1 @@ fun y -> hcom_template phi (`Atom y) (Value.act phi fhcom.cap)
        in
        Option.filter_map force_abs_face [diag] @ (ri_faces @ si_faces)
      in
      let boundary =
        Face.map @@ fun si s'i abs ->
        let phi = I.equate si s'i in
        hcom_template phi (I.act phi r') (Value.act phi (Abs.inst1 abs s'))
      in
      rigid_box fhcom.dir new_cap @@
      List.map boundary fhcom.sys

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
        let func = car equiv in
        let el1_cap = rigid_vproj x ~func ~el:cap in
        let el1_sys =
          let face =
            Face.map @@ fun ri r'i absi ->
            let phi = I.equate ri r'i in
            let yi, el = Abs.unleash absi in
            Abs.bind yi @@ vproj phi (I.act phi @@ `Atom x) ~func:(fun phi -> Value.act phi func) ~el
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
    | Pi _ | Sg _ ->
      make @@ GHCom {dir; ty; cap; sys}

    (* `Ext _`: the expansion will stop after a valid
     * correction system, so it is not so bad.
     *
     * `Up _`: perhaps we can have nghcom? *)
    | Ext _ | Univ _ | FHCom _ | V _ | Data _ | Up _ ->
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
              let ghcom00 = AbsFace.make phi r'i dim0 @@ fun phi -> Abs.act phi @@ Lazy.force absi in
              let ghcom01 =
                AbsFace.make phi r'i dim1 @@ fun phi ->
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
    (* Format.eprintf "rigid_com in: %a@.@." pp_abs abs; *)
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
      let sys = eval_bterm_boundary dlbl desc rho ~const_args ~rec_args ~rs constr.boundary in
      begin
        match force_val_sys sys with
        | `Proj v ->
          v
        | `Ok sys ->
          make @@ Intro {dlbl; clbl = info.clbl; const_args; rec_args; rs; sys}
      end

    | B.Var ix ->
      begin
        match Bwd.nth rho.cells ix with
        | `Val v -> v
        | cell ->
          let err = UnexpectedEnvCell cell in
          raise @@ E err
      end

  and eval_bterm_boundary dlbl desc rho ~const_args ~rec_args ~rs =
    List.map (eval_bterm_face dlbl desc rho ~const_args ~rec_args ~rs)

  and eval_bterm_face dlbl desc rho ~const_args ~rec_args ~rs (tr0, tr1, btm) =
    let rho' =
      Env.append rho @@
      (* ~~This is not backwards, FYI.~~ *)
      (* NARRATOR VOICE: it was backwards. *)
      List.map (fun x -> `Val x) const_args
      @ List.map (fun x -> `Val x) rec_args
      @ List.map (fun x -> `Dim x) rs
    in
    let r0 = eval_dim rho' tr0 in
    let r1 = eval_dim rho' tr1 in
    match Eq.make r0 r1 with
    | `Ok xi ->
      let v = lazy begin Value.act (I.equate r0 r1) @@ eval_bterm dlbl desc rho' btm end in
      Face.Indet (xi, v)
    | `Apart _ ->
      Face.False (r0, r1)
    | `Same _ ->
      let v = lazy begin eval_bterm dlbl desc rho' btm end in
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

    | Tm.Restrict tface ->
      let face = eval_tm_face rho tface in
      make @@ Restrict face

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
      make @@ ExtLam (nclo bnd rho)

    | Tm.RestrictThunk face ->
      let vface = eval_tm_face rho face in
      make @@ RestrictThunk vface

    | Tm.Cons (t0, t1) ->
      let v0 = eval rho t0 in
      let v1 = eval rho t1 in
      make @@ Cons (v0, v1)

    | Tm.FHCom info ->
      let r = eval_dim rho info.r in
      let r' = eval_dim rho info.r' in
      let dir = Dir.make r r' in
      let cap = eval rho info.cap in
      let sys = eval_rigid_bnd_sys rho info.sys in
      make_fhcom dir cap sys

    | Tm.Univ {kind; lvl} ->
      make @@ Univ {kind; lvl}

    | Tm.Box info ->
      let r = eval_dim rho info.r  in
      let r' = eval_dim rho info.r' in
      let dir = Dir.make r r' in
      let cap = eval rho info.cap in
      let sys = eval_rigid_tm_sys rho info.sys in
      make_box dir cap sys

    | (Tm.Dim0 | Tm.Dim1) ->
      raise @@ E (UnexpectedDimensionTerm tm)

    | Tm.Up cmd ->
      eval_cmd rho cmd

    | Tm.Let (cmd, Tm.B (_, t)) ->
      let v0 = eval_cmd rho cmd in
      eval (Env.snoc rho @@ `Val v0) t

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

    | Tm.Data lbl ->
      make @@ Data lbl

    | Tm.Intro (dlbl, clbl, args) ->
      let desc = Sig.lookup_datatype dlbl in
      let constr = Desc.lookup_constr clbl desc in
      let tconst_args, args = ListUtil.split (List.length constr.const_specs) args in
      let trec_args, trs = ListUtil.split (List.length constr.rec_specs) args in
      let const_args = List.map (eval rho) tconst_args in
      let rec_args = List.map (eval rho) trec_args in
      let rs = List.map (eval_dim rho) trs in
      make_intro (Env.clear_locals rho) ~dlbl ~clbl ~const_args ~rec_args ~rs

  and make_intro rho ~dlbl ~clbl ~const_args ~rec_args ~rs =
    let desc = Sig.lookup_datatype dlbl in
    let constr = Desc.lookup_constr clbl desc in
    let sys = eval_bterm_boundary dlbl desc rho ~const_args ~rec_args ~rs constr.boundary in
    match force_val_sys sys with
    | `Ok sys ->
      make @@ Intro {dlbl; clbl; const_args; rec_args; rs; sys}
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
    | Tm.RestrictForce ->
      restriction_force vhd
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
      let func phi0 = eval (Env.act phi0 rho) info.func in
      vproj I.idn r ~func ~el:vhd
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
    | Tm.Elim info ->
      let mot = clo info.mot rho in
      let clauses = List.map (fun (lbl, nbnd) -> lbl, nclo nbnd rho) info.clauses in
      elim_data info.dlbl ~mot ~scrut:vhd ~clauses


  and eval_head rho =
    function
    | Tm.Down info ->
      eval rho info.tm

    | Tm.DownX _ ->
      failwith "eval_head/DownX"

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
        match Bwd.nth rho.cells i with
        | `Val v -> v
        | cell ->
          let err = UnexpectedEnvCell cell in
          raise @@ E err
      end

    | Tm.Var info ->
      let tty, odef = Sig.lookup info.name info.twin in
      let rho' = Env.clear_locals rho in
      begin
        match odef with
        | Some def ->
          eval rho' @@ Tm.shift_univ info.ushift def
        | None ->
          let vty = eval rho' @@ Tm.shift_univ info.ushift tty in
          reflect vty (Var {name = info.name; twin = info.twin; ushift = info.ushift}) []
      end

    | Tm.Meta {name; ushift} ->
      let tty, odef = Sig.lookup name `Only in
      let rho' = Env.clear_locals rho in
      begin
        match odef with
        | Some def ->
          eval rho' @@ Tm.shift_univ ushift def
        | None ->
          let vty = eval rho' @@ Tm.shift_univ ushift tty in
          reflect vty (Meta {name; ushift}) []
      end

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
      let abs = lazy begin eval_bnd rho' bnd end in
      Face.Indet (xi, abs)
    | `Apart _ ->
      Face.False (sr, sr')
    | `Same _ ->
      let bnd = Option.get_exn obnd in
      let abs = lazy begin eval_bnd rho bnd end in
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
      let el = lazy begin eval rho' tm end in
      Face.Indet (xi, el)
    | `Apart _ ->
      Face.False (r, r')
    | `Same _ ->
      let tm = Option.get_exn otm in
      let el = lazy begin eval rho tm end in
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
    Abs.make1 @@ fun x ->
    let rho = Env.snoc rho @@ `Dim (`Atom x) in
    eval rho tm

  and eval_nbnd rho bnd =
    let Tm.NB (nms, tm) = bnd in
    let xs = Bwd.map Name.named nms in
    let rho = Env.append rho @@ Bwd.to_list @@ Bwd.map (fun x -> `Dim (`Atom x)) xs in
    Abs.bind xs @@ eval rho tm

  (* CORRECT *)
  and eval_ext_bnd rho bnd =
    let Tm.NB (nms, (tm, sys)) = bnd in
    let xs = Bwd.map Name.named nms in
    let rho = Env.append rho @@ Bwd.to_list @@ Bwd.map (fun x -> `Dim (`Atom x)) xs in
    let res = ExtAbs.bind xs (eval rho tm, eval_tm_sys rho sys) in
    res

  and unleash_data v =
    match unleash v with
    | Data dlbl -> dlbl
    | _ ->
      raise @@ E (UnleashDataError v)

  and unleash_pi v =
    match unleash v with
    | Pi {dom; cod} -> dom, cod
    | _ ->
      raise @@ E (UnleashPiError v)


  and unleash_later v =
    match unleash v with
    | Later clo -> clo
    | _ ->
      raise @@ E (UnleashLaterError v)

  and unleash_sg v =
    match unleash v with
    | Sg {dom; cod} -> dom, cod
    | _ ->
      raise @@ E (UnleashSgError v)

  and unleash_ext_with v rs =
    match unleash v with
    | Ext abs ->
      ExtAbs.inst abs (Bwd.from_list rs)
    | _ ->
      raise @@ E (UnleashExtError v)

  and unleash_v v =
    match unleash v with
    | V {x; ty0; ty1; equiv} ->
      x, ty0, ty1, equiv
    | _ ->
      raise @@ E (UnleashVError v)

  and unleash_lbl_ty v =
    match unleash v with
    | LblTy {lbl; args; ty} ->
      lbl, args, ty
    | _ ->
      raise @@ E (UnleashLblTyError v)

  and unleash_restriction_ty v =
    match unleash v with
    | Restrict face ->
      face
    | _ ->
      raise @@ E (UnleashRestrictError v)

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

  and restriction_force v =
    match unleash v with
    | RestrictThunk face ->
      begin
        match face with
        | Face.True (_, _, v) -> Lazy.force v
        | _ ->
          raise @@ E (ForcedUntrueRestriction face)
      end

    | Up info ->
      begin
        match unleash_restriction_ty info.ty with
        | Face.True (_, _, ty) ->
          let force = RestrictForce info.neu in
          let force_face =
            Face.map @@ fun _ _ a ->
            restriction_force a
          in
          let force_sys = List.map force_face info.sys in
          make @@ Up {ty = Lazy.force ty; neu = force; sys = force_sys}
        | _ as face ->
          raise @@ E (ForcedUntrueRestriction face)
      end

    | _ ->
      raise @@ E (ForcedUnexpectedRestriction v)

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
    | ExtLam nclo ->
      inst_nclo nclo @@ List.map (fun x -> `Dim x) ss

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
      let correction =
        let face = Face.map @@ fun _ _ v -> Abs.bind1 y v in
        List.map face forall_y_sys_s
      in
      let abs = Abs.bind1 y ty_s in
      let cap = ext_apply info.el ss in
      make_com (`Ok info.dir) abs cap @@ force_abs_sys correction

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
        | TickGen gen ->
          let neu = Fix (gen, dfix.ty, dfix.clo) in
          make @@ Up {ty = dfix.ty; neu; sys = []}
      end
    | DFixLine dfix ->
      begin
        match tick with
        | TickGen gen ->
          let neu = FixLine (dfix.x, gen, dfix.ty, dfix.clo) in
          let sys =
            let face0 =
              let xi = Eq.gen_const dfix.x `Dim0 in
              let phi = I.equate (`Atom dfix.x) `Dim0 in
              let body =
                lazy begin
                  let ty = Value.act phi dfix.ty in
                  let clo = Clo.act phi dfix.clo in
                  let neu = Fix (gen, ty, clo) in
                  (* check that this is right?? *)
                  reflect ty neu []
                end
              in
              Face.Indet (xi, body)
            in
            let face1 =
              let xi = Eq.gen_const dfix.x `Dim1 in
              let phi = I.equate (`Atom dfix.x) `Dim1 in
              let body =
                lazy begin
                  let ty = Value.act phi dfix.ty in
                  let clo = Clo.act phi dfix.clo in
                  inst_clo clo @@ make @@ DFix {ty; clo}
                end
              in
              Face.Indet (xi, body)
            in
            [face0; face1]
          in
          make @@ Up {ty = dfix.ty; neu; sys}
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
  and vproj phi mgen ~func ~el : value =
    match mgen with
    | `Atom x ->
      let phi0 = I.cmp (I.equate mgen `Dim0) phi in
      rigid_vproj x ~func:(func phi0) ~el
    | `Dim0 ->
      let func = func phi in
      apply func el
    | `Dim1 ->
      el

  and rigid_vproj x ~func ~el : value =
    match unleash el with
    | VIn info ->
      info.el1
    | Up up ->
      let z, ty0, ty1, equiv = unleash_v up.ty in
      let subst_0z = I.subst `Dim0 z in
      let ty0_0z = Value.act subst_0z ty0 in
      let ty1_0z = Value.act subst_0z ty1 in
      let func_nf =
        let func_ty = make_func ty0_0z ty0_0z in
        {ty = func_ty; el = func}
      in

      let neu = VProj {x; func = func_nf; neu = up.neu} in
      let vproj_face =
        Face.map @@ fun r r' a ->
        let phi = I.equate r r' in
        vproj phi (I.act phi @@ `Atom x) ~func:(fun phi0 -> Value.act phi0 func) ~el:a
      in
      let faces01 =
        let face0 =
          let xi = Eq.gen_const x `Dim0 in
          let phi = I.equate (`Atom x) `Dim0 in
          let body =
            lazy begin
              let func = Value.act phi func in
              apply func el
            end
          in
          Face.Indet (xi, body)
        in
        let face1 =
          let xi = Eq.gen_const x `Dim1 in
          let phi = I.equate (`Atom x) `Dim1 in
          Face.Indet (xi, lazy begin Value.act phi el end)
        in
        [face0; face1]
      in
      let vproj_sys = faces01 @ List.map vproj_face up.sys in
      make @@ Up {ty = ty1; neu; sys = vproj_sys}
    | _ ->
      let err = RigidVProjUnexpectedArgument el in
      raise @@ E err

  and elim_data dlbl ~mot ~scrut ~clauses =
    let find_clause clbl =
      try
        snd @@ List.find (fun (clbl', _) -> clbl = clbl') clauses
      with
      | Not_found ->
        raise @@ MissingElimClause clbl
    in

    match unleash scrut with
    | Intro info ->
      let nclo = find_clause info.clbl in

      (* Clean this up with some kind of a state type for the traversal maybe. Barf! *)
      let rec go cvs rvs rs =
        match cvs, rvs, rs with
        | v :: cvs, _, _->
          `Val v :: go cvs rvs rs
        | [], v :: rvs, _ ->
          let v_ih = elim_data dlbl ~mot ~scrut:v ~clauses in
          `Val v :: `Val v_ih :: go cvs rvs rs
        | [], [], r :: rs ->
          `Dim r :: go cvs rvs rs
        | [], [], [] ->
          []
      in
      inst_nclo nclo @@ go info.const_args info.rec_args info.rs

    | Up up ->
      let neu = Elim {dlbl; mot; neu = up.neu; clauses} in
      let mot' = inst_clo mot scrut in
      let elim_face =
        Face.map @@ fun r r' a ->
        let phi = I.equate r r' in
        let clauses' = List.map (fun (lbl, nclo) -> lbl, NClo.act phi nclo) clauses in
        elim_data dlbl ~mot:(Clo.act phi mot) ~scrut:a ~clauses:clauses'
      in
      let elim_sys = List.map elim_face up.sys in
      make @@ Up {ty = mot'; neu; sys = elim_sys}

    | FHCom info ->
      let tyabs =
        let r, _ = Dir.unleash info.dir in
        Abs.make1 @@ fun y ->
        inst_clo mot @@
        make_fhcom (Dir.make r @@ `Atom y) info.cap (`Ok info.sys)
      in
      let cap = elim_data dlbl ~mot ~scrut:info.cap ~clauses in
      let face =
        Face.map @@ fun r r' abs ->
        let y, ely = Abs.unleash1 abs in
        let phi = I.equate r r' in
        let clauses' = List.map (fun (lbl, nclo) -> lbl, NClo.act phi nclo) clauses in
        Abs.bind1 y @@
        elim_data dlbl ~mot:(Clo.act phi mot) ~scrut:ely ~clauses:clauses'
      in
      let sys = List.map face info.sys in
      rigid_com info.dir tyabs cap sys

    | _ ->
      raise @@ E (RecursorUnexpectedArgument ("data type", scrut))

  and car v =
    match unleash v with
    | Cons (v0, _) ->
      v0

    | Up info ->
      let dom, _ = unleash_sg info.ty in
      let car_sys = List.map (Face.map (fun _ _ -> car)) info.sys in
      make @@ Up {ty = dom; neu = Car info.neu; sys = car_sys}

    | Coe info ->
      let abs = flip Abs.unsafe_map info.abs @@ fun v -> fst @@ unleash_sg v in
      let el = car info.el in
      rigid_coe info.dir abs el

    | HCom info ->
      let dom, _ = unleash_sg info.ty in
      let cap = car info.cap in
      let face =
        Face.map @@ fun _ _ ->
        Abs.unsafe_map car
      in
      let sys = List.map face info.sys in
      rigid_hcom info.dir dom cap sys

    | GHCom info ->
      let dom, _ = unleash_sg info.ty in
      let cap = car info.cap in
      let face =
        Face.map @@ fun _ _ ->
        Abs.unsafe_map car
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
      let cdr_sys = List.map (Face.map (fun _ _ -> cdr)) info.sys in
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
        Abs.make1 @@ fun z ->
        let msys =
          let face =
            Face.map @@ fun _ _ ->
            Abs.unsafe_map car
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
        inst_clo cod hcom
      in
      let cap = cdr info.cap in
      let sys =
        let face =
          Face.map @@ fun _ _ ->
          Abs.unsafe_map cdr
        in
        List.map face info.sys
      in
      rigid_com info.dir abs cap sys

    | GHCom info ->
      let abs =
        Abs.make1 @@ fun z ->
        let r, _ = Dir.unleash info.dir in
        let dom, cod = unleash_sg info.ty in
        let msys =
          let face =
            Face.map @@ fun _ _ ->
            Abs.unsafe_map car
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
        inst_clo cod hcom
      in
      let cap = cdr info.cap in
      let sys =
        let face =
          Face.map @@ fun _ _ ->
          Abs.unsafe_map cdr
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
      let cap_sys =
        let face =
          Face.map @@ fun ri r'i a ->
          let phi = I.equate ri r'i in
          make_cap (Dir.act phi dir) (Value.act phi ty) (CompSys.act phi sys) a
        in
        List.map face info.sys
      in
      let faces =
        let face : ([`Rigid], _) face -> _ =
          function
          | Face.Indet (xi, abs) ->
            let body =
              lazy begin
                let s, s' = Eq.unleash xi in
                let phi = I.equate s s' in
                let dir' = Dir.act phi @@ Dir.swap dir in
                make_coe dir' (Lazy.force abs) @@ Value.act phi el
              end
            in
            Face.Indet (xi, body)
        in
        List.map face sys
      in
      make @@ Up {ty; neu = Cap {dir; neu = info.neu; ty; sys}; sys = faces @ cap_sys}
    | _ ->
      raise @@ E (RigidCapUnexpectedArgument el)


  and inst_clo clo varg : value =
    match clo with
    | Clo info ->
      let Tm.B (_, tm) = info.bnd in
      eval (Env.snoc info.rho @@ `Val varg) tm

  and inst_nclo nclo vargs : value =
    match nclo with
    | NClo info ->
      let Tm.NB (_, tm) = info.nbnd in
      eval (Env.append info.rho vargs) tm
    | NCloConst v ->
      Lazy.force v

  and inst_tick_clo clo tick =
    match clo with
    | TickClo info ->
      let Tm.B (_, tm) = info.bnd in
      eval (Env.snoc info.rho @@ `Tick tick) tm
    | TickCloConst v ->
      Lazy.force v

  and make_func ty0 ty1 : value =
    let rho = Env.append empty_env [`Val ty1; `Val ty0] in
    eval rho @@
    Tm.arr
      (Tm.up @@ Tm.ix 0)
      (Tm.up @@ Tm.ix 1)

  module Macro =
  struct
    let equiv ty0 ty1 : value =
      let rho = Env.append empty_env [`Val ty1; `Val ty0] in
      eval rho @@
      Tm.equiv
        (Tm.up @@ Tm.ix 0)
        (Tm.up @@ Tm.ix 1)

    let func = make_func

  end

end

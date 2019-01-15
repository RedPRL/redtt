open RedBasis
open Bwd
open Domain
open Combinators

include ValSig

type error =
  | UnexpectedEnvCell of env_el
  | ExpectedDimensionTerm of Tm.tm
  | InternalMortalityError
  | RigidCoeUnexpectedArgument of abs
  | RigidHComUnexpectedArgument of value
  | RigidGHComUnexpectedArgument of value
  | ApplyUnexpectedFunction of value
  | ApplyUnexpectedCube of value
  | RecursorUnexpectedArgument of string * value
  | SigmaProjUnexpectedArgument of string * value
  | RigidVProjUnexpectedArgument of atom * value
  | RigidCapUnexpectedArgument of value
  | UnexpectedDimensionTerm of Tm.tm
  | UnleashDataError of value
  | UnleashPiError of value
  | UnleashSgError of value
  | UnleashExtError of value
  | UnleashVError of value
  | UnleashRestrictError of value
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
    | RigidVProjUnexpectedArgument (x, v) ->
      Format.fprintf fmt
        "Unexpected argument to rigid vproj over dimension %a:@ %a."
        Name.pp x pp_value v
    | RigidCapUnexpectedArgument v ->
      Format.fprintf fmt
        "Unexpected argument to rigid cap:@ %a."
        pp_value v
    | UnexpectedEnvCell cell ->
      Format.fprintf fmt
        "Did not find what was expected in the environment: %a"
        pp_env_cell cell
    | ExpectedDimensionTerm t ->
      Format.fprintf fmt
        "Tried to evaluate non-dimension term %a as dimension."
        Tm.pp0 t
    | UnexpectedDimensionTerm t ->
      Format.fprintf fmt
        "Tried to evaluate dimension term %a as expression."
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
    | Tm.Up (hd, []) ->
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

    | Data info ->
      let params = List.map (Env.act_env_el phi) info.params in
      make @@ Data {info with params}

    | Intro info ->
      begin
        match force_val_sys @@ ValSys.act phi @@ ValSys.from_rigid info.sys with
        | `Ok sys ->
          let args = List.map (Env.act_env_el phi) info.args in
          make @@ Intro {info with args}
        | `Proj v ->
          v
      end

    | FortyTwo -> make FortyTwo

  and unleash : value -> con =
    fun (Node info) ->
      match info.action = I.idn with
      | true ->
        info.con
      | false ->
        let node' = act_can info.action info.con in
        let con = unleash node' in
        con

  and make_cons (a, b) =
    make @@ Cons (a, b)

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
    let validate : unit =
      if I.compare r r' = `Same then 
        begin
          Format.printf "oh n0!!!!!%a == %a @.@." I.pp  r I.pp r';
          failwith "bad!!!!!!!!!!!!!!!!!!"
        end
    in
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


  and realize_rec_spec ~dlbl ~params =
    function
    | Desc.Self ->
      make @@ Data {lbl = dlbl; params}

  and realize_rec_spec_ih ~dlbl ~params ~mot rspec scrut =
    match rspec with
    | Desc.Self ->
      inst_clo mot scrut


  (* TODO: check that this is right *)
  and rigid_multi_coe tyenv data_abs dir (x, specs) args =
    match specs, args with
    | [], [] ->
      []
    | (_, `Const spec) :: specs, `Val arg :: args ->
      let vty = eval tyenv spec in
      let r, r' = Dir.unleash dir in
      let coe_hd s = make_coe (Dir.make r s) (Abs.bind1 x vty) arg in
      let coe_tl =
        let coe_hd_x = coe_hd @@ `Atom x in
        rigid_multi_coe (Env.snoc tyenv @@ `Val coe_hd_x) data_abs dir (x, specs) args
      in
      `Val (coe_hd r') :: coe_tl
    | (_, `Rec Desc.Self) :: specs, `Val arg :: args ->
      let coe_hd = rigid_coe dir data_abs arg in
      let coe_tl = rigid_multi_coe (Env.snoc tyenv @@ `Val coe_hd) data_abs dir (x, specs) args in
      `Val (coe_hd) :: coe_tl
    | (_, `Dim) :: specs, `Dim s :: args ->
      `Dim s :: rigid_multi_coe (Env.snoc tyenv @@ `Dim s) data_abs dir (x, specs) args
    | _ ->
      failwith "rigid_multi_coe: length mismatch"

  and multi_coe env data_abs mdir (x, specs) args =
    match mdir with
    | `Ok dir ->
      rigid_multi_coe env data_abs dir (x, specs) args
    | `Same _ ->
      args

  (* Figure 8 of Part IV: https://arxiv.org/abs/1801.01568v3; specialized to non-indexed HITs. *)
  and rigid_coe_nonstrict_data_intro dir abs ~dlbl ~params ~clbl args =
    let x = Name.fresh () in
    let desc = Sig.lookup_datatype dlbl in
    let constr = Desc.lookup_constr clbl @@ Desc.constrs desc in

    let r, r' = Dir.unleash dir in

    let args_in_dir dir = multi_coe (Env.append empty_env params) abs dir (x, Desc.Constr.specs constr) args in
    let intro = make_intro ~dlbl ~params ~clbl @@ args_in_dir @@ `Ok dir in

    let boundary = Desc.Constr.boundary constr in

    begin
      match boundary with
      | [] ->
        intro
      | _ ->
        let faces =
          let rho = Env.append (Env.append empty_env params) @@ args_in_dir @@ Dir.make r (`Atom x) in
          eval_tm_sys rho boundary
        in
        let fix_face =
          Face.map @@ fun s s' el ->
          let phi = I.equate s s' in
          Abs.bind1 x @@ make_coe (Dir.make (`Atom x) r') (Abs.act phi abs) el
        in
        let correction = List.map fix_face faces in
        make_fhcom (`Ok (Dir.swap dir)) intro @@ force_abs_sys correction
    end

  and rigid_coe_nonstrict_data dir abs el =
    let _, tyx = Abs.unsafe_unleash abs in
    match unleash tyx, unleash el with
    | Data data, Intro info ->
      rigid_coe_nonstrict_data_intro dir abs ~dlbl:data.lbl ~params:data.params ~clbl:info.clbl info.args

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
    | Pi _ | Sg _ | Ext _ ->
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

    | Data data ->
      let desc = Sig.lookup_datatype data.lbl in
      if Desc.is_strict_set desc then el
      else
        begin
          (* for data types without parameters, coe can be the identity *)
          match desc.body with
          | Desc.TNil _ ->
            el
          | _ ->
            rigid_coe_nonstrict_data dir abs el
        end

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
      (* Note that the algorithm in Part III cannot be used here
       * because we are working with open terms. *)

      (* [Y]: yacctt 073694948042342d55cea64a42d2076365800ee4. *)

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
              ~func:(fun phi0 -> Value.act phi0 @@ subst_src @@ do_fst info.equiv)
              ~el:(Value.act phi el)
          in

          (* Some helper functions to reduce typos. *)
          let base0 phi dest = base phi `Dim0 dest in
          let base1 phi dest = base phi `Dim1 dest in
          let fiber0 phi b = do_fst @@ apply (do_snd (Value.act phi equiv0)) b in

          (* This gives a path from the fiber `fib` to `fiber0 b`
           * where `b` is calculated from `fib` as
           * `ext_apply (do_snd fib) [`Dim1]` directly. *)
          let contr0 phi fib = apply (do_snd @@ apply (do_snd (Value.act phi equiv0)) (ext_apply (do_snd fib) [`Dim1])) fib in

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

          (* This is the type of the fiber, and is used for
           * simplifying the generating code for the front face
           * (r'=0). It is using the evaluator to generate the
           * type in the semantic domain. *)
          let fiber0_ty phi b =
            let var i = Tm.up @@ Tm.ix i in
            let env = Env.append empty_env [`Val b; `Val (do_fst (Value.act phi equiv0)); `Val (Value.act phi ty10); `Val (Value.act phi ty00)] in
            eval env @@ Tm.fiber ~ty0:(var 0) ~ty1:(var 1) ~f:(var 2) ~x:(var 3)
          in

          (* This is to generate the element in `ty0` and also
           * the face for r'=0. This is `O` in [F]. *)
          let fixer_fiber phi =
            (* Turns out `fiber_at_face0` will be
             * used for multiple times. *)
            let rphi = I.act phi r in
            let fiber_at_face0 phi =
              make_cons
                (Value.act phi el,
                 make @@ ExtLam (NCloConst (lazy begin base0 phi `Dim0 end)))
            in

            (* The implementation used in [Y]. *)
            (* hcom whore cap is (fiber0 base), r=0 face is contr0, and r=1 face is constant *)
            make_hcom (Dir.make `Dim1 `Dim0) (fiber0_ty phi (base phi rphi `Dim0)) (fiber0 phi (base phi rphi `Dim0)) @@
            force_abs_sys @@
            let face0 =
              AbsFace.make phi rphi `Dim0 @@ fun phi ->
              Abs.make1 @@ fun w -> ext_apply (contr0 phi (fiber_at_face0 phi)) [`Atom w]
            in
            let face1 =
              AbsFace.make phi rphi `Dim1 @@ fun phi ->
              Abs.make1 @@ fun _ -> fiber0 phi (base1 phi `Dim0)
            in
            [face0; face1]
          in

          let el0 phi0 = do_fst (fixer_fiber phi0) in

          let face_front =
            AbsFace.make I.idn r' `Dim0 @@ fun phi ->
            Abs.make1 @@ fun w -> ext_apply (do_snd (fixer_fiber phi)) [`Atom w]
          in

          let el1 =
            make_hcom (Dir.make `Dim1 r') (subst_r' info.ty1) (base I.idn r r') @@
            force_abs_sys [face0; face_diag; face_front]
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
              let funcr = Value.act phi @@ do_fst info.equiv in
              rigid_vproj info.x ~func:funcr ~el
            in
            let sys =
              let face0 =
                AbsFace.gen_const I.idn info.x `Dim0 @@ fun phi ->
                Abs.bind1 x @@ apply (do_fst info.equiv) @@
                make_coe (Dir.make (I.act phi r) (`Atom x)) (Abs.act phi abs0) (Value.act phi el)
              in
              let face1 =
                AbsFace.gen_const I.idn info.x `Dim1 @@ fun phi ->
                Abs.bind1 x @@
                make_coe (Dir.make (I.act phi r) (`Atom x)) (Abs.act phi abs1) (Value.act phi el)
              in
              Option.filter_map force_abs_face [face0; face1]
            in
            rigid_com dir abs1 cap sys
          in
          rigid_vin info.x el0 el1
      end

    | _ ->
      let err = RigidCoeUnexpectedArgument abs in
      raise @@ E err


  and rigid_nhcom_up_at_type dir univ ty cap ~comp_sys ~rst_sys =
    let neu = NHComAtType {dir; univ; ty; ty_sys = rst_sys; cap; sys = comp_sys} in
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
        let func = do_fst equiv in
        let el1_cap = rigid_vproj x ~func ~el:cap in
        let face0 =
          AbsFace.gen_const I.idn x `Dim0 @@ fun phi ->
          Abs.make1 @@ fun y ->
          apply func @@ hcom phi (`Atom y) ty0 (* ty0 is already under `phi0` *)
        in
        let el1_sys =
          let face =
            Face.map @@ fun ri r'i absi ->
            let phi = I.equate ri r'i in
            let yi, el = Abs.unleash absi in
            Abs.bind yi @@ vproj phi (I.act phi @@ `Atom x) ~func:(fun phi -> Value.act phi func) ~el
          in
          Option.filter_map force_abs_face [face0] @ List.map face sys
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
                make_ghcom (Dir.make (I.act phi r) (`Atom y)) (Value.act phi ty) (Value.act phi cap) @@
                (* XXX this would stop the expansion early, but is
                 * unfortunately duplicate under `AbsFace.make` *)
                CompSys.act phi rest0
              in
              match force_abs_sys [ghcom00; ghcom01] with
              | `Proj abs -> abs
              | `Ok faces ->
                Abs.make1 @@ fun y ->
                make_hcom (Dir.make (I.act phi r) (`Atom y)) (Value.act phi ty) (Value.act phi cap) (`Ok (faces @ rest0))
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

    | Tm.Data info ->
      let params = List.map (fun tm -> `Val (eval rho tm)) info.params in
      make @@ Data {lbl = info.lbl; params}

    | Tm.Intro (dlbl, clbl, params, args) ->
      let desc = Sig.lookup_datatype dlbl in
      let constr = Desc.lookup_constr clbl @@ Desc.constrs desc in
      let vparams = List.map (fun tm -> `Val (eval rho tm)) params in
      let rec go args specs =
        match args, specs with
        | arg :: args, (_, (`Const _ | `Rec _)) :: specs ->
          let v = eval rho arg in
          `Val v :: go args specs
        | arg :: args, (_, `Dim) :: specs ->
          let r = eval_dim rho arg in
          `Dim r :: go args specs
        | [], [] ->
          []
        | _ ->
          failwith "eval/intro: length mismatch"
      in
      make_intro ~dlbl ~params:vparams ~clbl @@ go args @@ Desc.Constr.specs constr

    | Tm.FortyTwo -> make FortyTwo

  and make_intro ~dlbl ~params ~clbl (args : env_el list) : value =
    let desc = Sig.lookup_datatype dlbl in
    let constr = Desc.lookup_constr clbl @@ Desc.constrs desc in
    let sys = eval_tm_sys (Env.append empty_env (params @ args)) @@ Desc.Constr.boundary constr in
    match force_val_sys sys with
    | `Ok sys ->
      make @@ Intro {dlbl; clbl; args; sys}
    | `Proj v ->
      v

  and eval_cmd rho (hd, sp) =
    let vhd = eval_head rho hd in
    eval_stack rho vhd sp

  and eval_stack rho vhd =
    function
    | [] -> vhd
    | frm :: stk ->
      let vhd = eval_frame rho vhd frm in
      eval_stack rho vhd stk

  and eval_frame rho vhd =
    function
    | Tm.RestrictForce ->
      restriction_force vhd
    | Tm.FunApp t ->
      let v = eval rho t in
      apply vhd v
    | Tm.ExtApp ts ->
      let rs = List.map (eval_dim rho) ts in
      ext_apply vhd rs
    | Tm.Fst ->
      do_fst vhd
    | Tm.Snd ->
      do_snd vhd
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
    | Tm.Elim info ->
      let mot = clo info.mot rho in
      let clauses = List.map (fun (lbl, nbnd) -> lbl, nclo nbnd rho) info.clauses in
      let params = List.map (fun tm -> `Val (eval rho tm)) info.params in
      elim_data ~dlbl:info.dlbl ~params ~mot ~scrut:vhd ~clauses


  and eval_head rho =
    function
    | Tm.Down info ->
      eval rho info.tm

    | Tm.DownX _ ->
      failwith "eval_head/DownX"

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
        | exception exn ->
          Printexc.print_raw_backtrace stderr (Printexc.get_callstack 20);
          Format.eprintf "@.";
          raise exn
      end

    | Tm.Var info ->
      let tty, odef = Sig.lookup_with_twin info.name info.twin in
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
      let tty, odef = Sig.lookup_with_twin name `Only in
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

  and eval_bnd_face rho (tr, tr', bnd) =
    let sr = eval_dim rho tr in
    let sr' = eval_dim rho tr' in
    match Eq.make sr sr' with
    | `Ok xi ->
      let rho' = Env.act (I.equate sr sr') rho in
      let abs = lazy begin eval_bnd rho' bnd end in
      Face.Indet (xi, abs)
    | `Apart _ ->
      Face.False (sr, sr')
    | `Same _ ->
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

  and eval_tm_face rho (tr, tr', tm) : val_face =
    let r = eval_dim rho tr in
    let r' = eval_dim rho tr' in
    match Eq.make r r' with
    | `Ok xi ->
      let rho' = Env.act (I.equate r r') rho in
      (* The problem here is that the this is not affecting GLOBALS! *)
      let el = lazy begin eval rho' tm end in
      Face.Indet (xi, el)
    | `Apart _ ->
      Face.False (r, r')
    | `Same _ ->
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
    | Data info -> info.lbl
    | _ ->
      raise @@ E (UnleashDataError v)

  and unleash_pi v =
    match unleash v with
    | Pi {dom; cod} -> dom, cod
    | _ ->
      raise @@ E (UnleashPiError v)


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

  and unleash_restriction_ty v =
    match unleash v with
    | Restrict face ->
      face
    | _ ->
      raise @@ E (UnleashRestrictError v)

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
        let face0  =
          ValFace.gen_const I.idn x `Dim0 @@ fun phi ->
          apply (Value.act phi func) @@ Value.act phi el
        in
        let face1 =
          ValFace.gen_const I.idn x `Dim1 @@ fun phi ->
          Value.act phi el
        in
        [face0; face1]
      in
      let vproj_sys = faces01 @ List.map vproj_face up.sys in
      make @@ Up {ty = ty1; neu; sys = vproj_sys}
    | _ ->
      let err = RigidVProjUnexpectedArgument (x, el) in
      raise @@ E err

  and elim_data ~dlbl ~params ~mot ~scrut ~clauses =
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

      let desc = Sig.lookup_datatype dlbl in
      let constr = Desc.lookup_constr info.clbl @@ Desc.constrs desc in

      let rec go args specs =
        match args, specs with
        | cell :: args , (_, `Const _) :: specs ->
          cell :: go args specs
        | `Val v :: args, (_, `Rec Desc.Self) :: specs ->
          (* What do I do here if not Desc.Self??? *)
          let v_ih = elim_data ~dlbl ~params ~mot ~scrut:v ~clauses in
          `Val v :: `Val v_ih :: go args specs
        | cell :: args, (_, `Dim) :: specs ->
          cell :: go args specs
        | [], [] ->
          []
        | _ ->
          failwith "elim_data: length mismatch"
      in

      inst_nclo nclo @@ go info.args @@ Desc.Constr.specs constr

    | Up up ->
      let neu = Elim {dlbl; params; mot; neu = up.neu; clauses} in
      let mot' = inst_clo mot scrut in
      let elim_face =
        Face.map @@ fun r r' a ->
        let phi = I.equate r r' in
        let clauses' = List.map (fun (lbl, nclo) -> lbl, NClo.act phi nclo) clauses in
        elim_data ~dlbl ~params ~mot:(Clo.act phi mot) ~scrut:a ~clauses:clauses'
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
      let cap = elim_data ~dlbl ~params ~mot ~scrut:info.cap ~clauses in
      let face =
        Face.map @@ fun r r' abs ->
        let y, ely = Abs.unleash1 abs in
        let phi = I.equate r r' in
        let clauses' = List.map (fun (lbl, nclo) -> lbl, NClo.act phi nclo) clauses in
        let params' = List.map (Env.act_env_el phi) params in
        Abs.bind1 y @@
        elim_data ~dlbl ~params:params' ~mot:(Clo.act phi mot) ~scrut:ely ~clauses:clauses'
      in
      let sys = List.map face info.sys in
      rigid_com info.dir tyabs cap sys

    | _ ->
      raise @@ E (RecursorUnexpectedArgument ("data type", scrut))

  and do_fst v =
    match unleash v with
    | Cons (v0, _) ->
      v0

    | Up info ->
      let dom, _ = unleash_sg info.ty in
      let fst_sys = List.map (Face.map (fun _ _ -> do_fst)) info.sys in
      make @@ Up {ty = dom; neu = Fst info.neu; sys = fst_sys}

    | Coe info ->
      let abs = flip Abs.unsafe_map info.abs @@ fun v -> fst @@ unleash_sg v in
      let el = do_fst info.el in
      rigid_coe info.dir abs el

    | HCom info ->
      let dom, _ = unleash_sg info.ty in
      let cap = do_fst info.cap in
      let face =
        Face.map @@ fun _ _ ->
        Abs.unsafe_map do_fst
      in
      let sys = List.map face info.sys in
      rigid_hcom info.dir dom cap sys

    | GHCom info ->
      let dom, _ = unleash_sg info.ty in
      let cap = do_fst info.cap in
      let face =
        Face.map @@ fun _ _ ->
        Abs.unsafe_map do_fst
      in
      let sys = List.map face info.sys in
      rigid_ghcom info.dir dom cap sys

    | _ ->
      raise @@ E (SigmaProjUnexpectedArgument ("do_fst", v))

  and do_snd v =
    match unleash v with
    | Cons (_, v1) ->
      v1

    | Up info ->
      let _, cod = unleash_sg info.ty in
      let snd_sys = List.map (Face.map (fun _ _ -> do_snd)) info.sys in
      let cod_car = inst_clo cod @@ do_fst v in
      make @@ Up {ty = cod_car; neu = Snd info.neu; sys = snd_sys}

    | Coe info ->
      let abs =
        let x, tyx = Abs.unleash1 info.abs in
        let domx, codx = unleash_sg tyx in
        let r, _ = Dir.unleash info.dir in
        let coerx =
          make_coe
            (Dir.make r (`Atom x))
            (Abs.bind1 x domx)
            (do_fst info.el)
        in
        Abs.bind1 x @@ inst_clo codx coerx
      in
      let el = do_snd info.el in
      rigid_coe info.dir abs el

    | HCom info ->
      let abs =
        let r, _ = Dir.unleash info.dir in
        let dom, cod = unleash_sg info.ty in
        Abs.make1 @@ fun z ->
        let msys =
          let face =
            Face.map @@ fun _ _ ->
            Abs.unsafe_map do_fst
          in
          `Ok (List.map face info.sys)
        in
        let hcom =
          make_hcom
            (Dir.make r (`Atom z))
            dom
            (do_fst info.cap)
            msys
        in
        inst_clo cod hcom
      in
      let cap = do_snd info.cap in
      let sys =
        let face =
          Face.map @@ fun _ _ ->
          Abs.unsafe_map do_snd
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
            Abs.unsafe_map do_fst
          in
          `Ok (List.map face info.sys)
        in
        let hcom =
          make_ghcom
            (Dir.make r (`Atom z))
            dom
            (do_fst info.cap)
            msys
        in
        inst_clo cod hcom
      in
      let cap = do_snd info.cap in
      let sys =
        let face =
          Face.map @@ fun _ _ ->
          Abs.unsafe_map do_snd
        in
        List.map face info.sys
      in
      rigid_gcom info.dir abs cap sys

    | _ ->
      raise @@ E (SigmaProjUnexpectedArgument ("do_snd", v))

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
      let Tm.NB (nms, tm) = info.nbnd in
      if Bwd.length nms != List.length vargs then failwith "inst_nclo: incorrect length";
      eval (Env.append info.rho vargs) tm
    | NCloConst v ->
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

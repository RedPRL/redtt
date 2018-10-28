open Domain
open RedBasis
open Bwd
open BwdNotation

module D = Domain

module Env :
sig
  type t

  val len : t -> int

  val emp : t
  val make : int -> t
  val succ : t -> t
  val succn : int -> t -> t
  val abs : t -> Name.t list -> t

  val ix_of_lvl : int -> t -> int
  val ix_of_atom : Name.t -> t -> int
end =
struct
  module M = Map.Make (Name)
  type t = {n : int; atoms : int M.t}

  let len env =
    env.n

  let make n =
    {n; atoms = M.empty}

  let emp = make 0

  let succ env =
    {env with n = env.n + 1}

  let succn n env =
    {env with n = env.n + n}

  let abs1 env x =
    {n = env.n + 1;
     atoms = M.add x env.n env.atoms}
  (* TODO: should that be env.n + 1? *)

  (* I might be doing this backwards ;-) *)
  let rec abs env xs =
    match xs with
    | [] -> env
    | x :: xs -> abs (abs1 env x) xs

  let ix_of_lvl l env =
    env.n - (l + 1)

  let ix_of_atom x env =
    try
      let lvl = M.find x env.atoms in
      ix_of_lvl lvl env
    with _ -> failwith "ix_of_atom"
end

type env = Env.t

module type S =
sig
  val quote_nf : env -> nf -> Tm.tm
  val quote_neu : env -> neu -> Tm.tm Tm.cmd
  val quote_ty : env -> value -> Tm.tm
  val quote_val_sys : env -> value -> val_sys -> (Tm.tm, Tm.tm) Tm.system
  val equate_data_params : env -> Name.t -> Desc.body -> env_el list -> env_el list -> Tm.tm list
  val quote_data_params : env -> Name.t -> Desc.body -> env_el list -> Tm.tm list

  val quote_dim : env -> I.t -> Tm.tm

  val equiv : env -> ty:value -> value -> value -> unit
  val equiv_ty : env -> value -> value -> unit
  val equiv_dim : env -> I.t -> I.t -> unit
  val equiv_data_params : env -> Name.t -> Desc.body -> env_el list -> env_el list -> unit
  val subtype : env -> value -> value -> unit

  val approx_restriction : env -> value -> value -> val_sys -> val_sys -> unit
end



type error =
  | UnequalNf of {env : Env.t; ty : value; el0 : value; el1 : value}
  | UnequalNeu of {env : Env.t; neu0 : neu; neu1 : neu}
  | UnequalLbl of Name.t * Name.t
  | UnequalDim of I.t * I.t

let pp_error fmt =
  function
  | UnequalNf {ty; el0; el1; _} ->
    Format.fprintf fmt "@[<hv>%a@ %a %a@ : %a@]"
      Domain.pp_value el0
      Uuseg_string.pp_utf_8 "≠"
      Domain.pp_value el1 Domain.pp_value ty

  | UnequalNeu {neu0; neu1; _} ->
    Format.fprintf fmt "@[<hv>%a@ %a@ %a@]"
      Domain.pp_neu neu0
      Uuseg_string.pp_utf_8 "≠"
      Domain.pp_neu neu1

  | UnequalLbl (lbl0, lbl1) ->
    Format.fprintf fmt "@[<hv>%a@ %a@ %a@]"
      Name.pp lbl0
      Uuseg_string.pp_utf_8 "≠"
      Name.pp lbl1

  | UnequalDim (r0, r1) ->
    Format.fprintf fmt "@[<hv>Dimensions@ %a@ %a@ %a@]"
      I.pp r0
      Uuseg_string.pp_utf_8 "≠"
      I.pp r1

exception E of error

module Error =
struct
  type t = error
  let pp = pp_error
  exception E = E
end

let _ =
  PpExn.install_printer @@ fun fmt ->
  function
  | E err ->
    Format.fprintf fmt "@[<1>%a@]" pp_error err
  | _ ->
    raise PpExn.Unrecognized


module M (V : Val.S) : S =
struct
  module QEnv = Env
  open V
  module Env = QEnv

  let generic_constrained env ty sys =
    reflect ty (Lvl (None, Env.len env)) sys

  let generic env ty =
    generic_constrained env ty []

  let rec equate env ty el0 el1 =
    match unleash ty, unleash el0, unleash el1 with
    | _, Up up0, Up up1 ->
      Tm.up @@ equate_neu env up0.neu up1.neu

    | Pi {dom; cod}, _, _ ->
      let var = generic env dom in
      let vcod = inst_clo cod var in
      let app0 = apply el0 var in
      let app1 = apply el1 var in
      Tm.lam (clo_name cod) @@ equate (Env.succ env) vcod app0 app1

    | Sg {dom; cod}, _, _ ->
      let el00 = do_fst el0 in
      let el10 = do_fst el1 in
      let q0 = equate env dom el00 el10 in
      let vcod = inst_clo cod el00 in
      let q1 = equate env vcod (do_snd el0) (do_snd el1) in
      Tm.cons q0 q1

    | Ext abs, _, _ ->
      let xs, (tyx, _) = Domain.ExtAbs.unleash abs in
      let xs_fwd = Bwd.to_list xs in
      let rs = List.map (fun x -> `Atom x) xs_fwd in
      let app0 = ext_apply el0 rs in
      let app1 = ext_apply el1 rs in
      Tm.ext_lam (Bwd.map Name.name xs) @@
      equate (Env.abs env xs_fwd) tyx app0 app1

    | Restrict face, _, _ ->
      begin
        match face with
        | Face.False (r, r') ->
          let tr = quote_dim env r in
          let tr' = quote_dim env r' in
          Tm.make @@ Tm.RestrictThunk (tr, tr', Tm.forty_two)

        | Face.True (r, r', ty) ->
          let tr = quote_dim env r in
          let tr' = quote_dim env r' in
          let force0 = restriction_force el0 in
          let force1 = restriction_force el1 in
          let tm = equate env (Lazy.force ty) force0 force1 in
          Tm.make @@ Tm.RestrictThunk (tr, tr', tm)

        | Face.Indet (p, ty) ->
          let r, r' = Eq.unleash p in
          let tr = quote_dim env r in
          let tr' = quote_dim env r' in
          let phi = I.equate r r' in
          let force0 = restriction_force @@ Domain.Value.act phi el0 in
          let force1 = restriction_force @@ Domain.Value.act phi el1 in
          let tm = equate env (Lazy.force ty) force0 force1 in
          Tm.make @@ Tm.RestrictThunk (tr, tr', tm)
      end

    | V info, _, _ ->
      let tr = quote_dim env @@ `Atom info.x in
      let phi_r0 = I.equate `Dim0 (`Atom info.x) in
      let tm0 = equate env (Domain.Value.act phi_r0 info.ty0) (Domain.Value.act phi_r0 el0) (Domain.Value.act phi_r0 el1) in
      let func = do_fst info.equiv in
      let vproj0 = rigid_vproj info.x ~func ~el:el0 in
      let vproj1 = rigid_vproj info.x ~func ~el:el1 in
      let tm1 = equate env info.ty1 vproj0 vproj1 in
      Tm.make @@ Tm.VIn {r = tr; tm0; tm1}

    | FHCom info, _, _ ->
      let s, s' = Dir.unleash info.dir in
      let ts, ts' = quote_dim env s, quote_dim env s' in

      let cap0 = rigid_cap info.dir info.cap info.sys el0 in
      let cap1 = rigid_cap info.dir info.cap info.sys el1 in
      let tcap = equate env info.cap cap0 cap1 in

      let quote_boundary : rigid_abs_face -> (Tm.tm, Tm.tm) Tm.face = function
        | Face.Indet (p, abs) ->
          let ri, ri' = Eq.unleash p in
          let phi = I.equate ri ri' in
          let tri, tri' = quote_dim env ri, quote_dim env ri' in
          let b = equate env (Abs.inst1 (Lazy.force abs) s') (Value.act phi el0) (Value.act phi el1) in
          tri, tri', b
      in
      let tsys = List.map quote_boundary info.sys in

      Tm.make @@ Tm.Box {r = ts; r' = ts'; cap = tcap; sys = tsys}

    | _, Univ info0, Univ info1 ->
      if info0.kind = info1.kind && info0.lvl = info1.lvl then
        Tm.univ ~kind:info0.kind ~lvl:info0.lvl
      else
        failwith "Expected equal universe levels"

    | _, Pi pi0, Pi pi1 ->
      let dom = equate env ty pi0.dom pi1.dom in
      let var = generic env pi0.dom in
      let vcod0 = inst_clo pi0.cod var in
      let vcod1 = inst_clo pi1.cod var in
      let cod = equate (Env.succ env) ty vcod0 vcod1 in
      Tm.pi (clo_name pi0.cod) dom cod

    | _, Data info0, Data info1 ->
      if info0.lbl = info1.lbl then
        let lbl = info0.lbl in
        let desc = Sig.lookup_datatype lbl in
        let params = equate_data_params env lbl desc.body info0.params info1.params in
        Tm.make @@ Tm.Data {lbl; params}
      else
        raise @@ E (UnequalLbl (info0.lbl, info1.lbl))

    | _, Sg sg0, Sg sg1 ->
      let dom = equate env ty sg0.dom sg1.dom in
      let var = generic env sg0.dom in
      let vcod0 = inst_clo sg0.cod var in
      let vcod1 = inst_clo sg1.cod var in
      let cod = equate (Env.succ env) ty vcod0 vcod1 in
      Tm.sg (clo_name sg0.cod) dom cod

    | _, Ext abs0, Ext abs1 ->
      let xs, (ty0x, sys0x) = Domain.ExtAbs.unleash abs0 in
      let xs_fwd = Bwd.to_list xs in
      let ty1x, sys1x = Domain.ExtAbs.inst abs1 @@ Bwd.map (fun x -> `Atom x) xs in
      let envx = Env.abs env xs_fwd in
      let tyx = equate envx ty ty0x ty1x in
      let sysx = equate_val_sys envx ty0x sys0x sys1x in
      Tm.make @@ Tm.Ext (Tm.NB (Bwd.map Name.name xs, (tyx, sysx)))

    | _, Restrict face0, Restrict face1 ->
      let univ = D.make @@ Univ {lvl = `Omega; kind = `Pre} in
      let face = equate_val_face env univ face0 face1 in
      Tm.make @@ Tm.Restrict face

    | _, V info0, V info1 ->
      let x0 = info0.x in
      let x1 = info1.x in
      let tr = equate_atom env x0 x1 in
      let ty0 = equate_ty env info0.ty0 info1.ty0 in
      let ty1 = equate_ty env info0.ty1 info1.ty1 in
      let equiv_ty = V.Macro.equiv info0.ty0 info1.ty1 in
      let equiv = equate env equiv_ty info0.equiv info1.equiv in
      Tm.make @@ Tm.V {r = tr; ty0; ty1; equiv}

    | _, FHCom fhcom0, FHCom fhcom1 ->
      let tr, tr' = equate_dir env fhcom0.dir fhcom1.dir in
      let cap = equate env ty fhcom0.cap fhcom1.cap in
      let sys = equate_comp_sys env ty fhcom0.sys fhcom1.sys in
      Tm.make @@ Tm.FHCom {r = tr; r' = tr'; cap; sys}

    | _, HCom hcom0, HCom hcom1 ->
      begin
        try
          let tr, tr' = equate_dir env hcom0.dir hcom1.dir in
          let ty = equate_ty env hcom0.ty hcom1.ty in
          let cap = equate env hcom0.ty hcom0.cap hcom1.cap in
          let sys = equate_comp_sys env hcom0.ty hcom0.sys hcom1.sys in
          Tm.up (Tm.HCom {r = tr; r' = tr'; ty; cap; sys}, [])
        with
        | exn -> Format.eprintf "equating: %a <> %a@." pp_value el0 pp_value el1; raise exn
      end

    | _, Coe coe0, Coe coe1 ->
      let tr, tr' = equate_dir env coe0.dir coe1.dir in
      let univ = make @@ Univ {kind = `Pre; lvl = `Omega} in
      let bnd = equate_val_abs env univ coe0.abs coe1.abs in
      let tyr =
        let r, _ = Dir.unleash coe0.dir in
        Abs.inst1 coe0.abs r
      in
      let tm = equate env tyr coe0.el coe1.el in
      Tm.up (Tm.Coe {r = tr; r' = tr'; ty = bnd; tm}, [])

    | _, GHCom ghcom0, GHCom ghcom1 ->
      begin
        try
          let tr, tr' = equate_dir env ghcom0.dir ghcom1.dir in
          let ty = equate_ty env ghcom0.ty ghcom1.ty in
          let cap = equate env ghcom0.ty ghcom0.cap ghcom1.cap in
          let sys = equate_comp_sys env ghcom0.ty ghcom0.sys ghcom1.sys in
          Tm.up (Tm.GHCom {r = tr; r' = tr'; ty; cap; sys}, [])
        with
        | exn -> Format.eprintf "equating: %a <> %a@." pp_value el0 pp_value el1; raise exn
      end

    | Data data, Intro info0, Intro info1 when info0.clbl = info1.clbl ->
      let desc = V.Sig.lookup_datatype data.lbl in
      let params = equate_data_params env data.lbl desc.body data.params data.params in
      let constr = Desc.lookup_constr info0.clbl @@ Desc.constrs desc in
      let tms = equate_constr_args env data.lbl data.params constr info0.args info1.args in
      Tm.make @@ Tm.Intro (data.lbl, info0.clbl, params, tms)

    | _ ->
      (* For more readable error messages *)
      let el0 = D.make @@ V.unleash el0 in
      let el1 = D.make @@ V.unleash el1 in
      let err = UnequalNf {env; ty; el0; el1} in
      raise @@ E err

  and quote_data_params env dlbl tele cells =
    equate_data_params env dlbl tele cells cells

  and equate_data_params env dlbl tele cells0 cells1 =
    let rec go acc tyenv tele cells0 cells1 =
      match tele, cells0, cells1 with
      | Desc.TNil _, [], [] ->
        Bwd.to_list acc

      | Desc.TCons (ty, Tm.B (_, tele)), `Val v0 :: cells0, `Val v1 :: cells1 ->
        let vty = V.eval tyenv ty in
        let tm = equate env vty v0 v1 in
        let tyenv = D.Env.snoc tyenv (`Val v0) in
        go (acc #< tm) tyenv tele cells0 cells1

      | _ ->
        failwith "equate_data_params: length mismatch"
    in
    go Emp empty_env tele cells0 cells1

  and equate_constr_args env dlbl params constr cells0 cells1 =
    let rec go acc venv specs cells0 cells1 =
      match specs, cells0, cells1 with
      | (_, `Const ty) :: specs, `Val el0 :: cells0, `Val el1 :: cells1 ->
        let vty = eval venv ty in
        let tm0 = equate env vty el0 el1 in
        go (acc #< tm0) (D.Env.snoc venv @@ `Val el0) specs cells0 cells1

      | (_, `Rec rspec) :: specs, `Val el0 :: cells0, `Val el1 :: cells1 ->
        let vty = V.realize_rec_spec ~dlbl ~params rspec in
        let tm0 = equate env vty el0 el1 in
        go (acc #< tm0) (D.Env.snoc venv @@ `Val el0) specs cells0 cells1

      | (_, `Dim) :: specs, `Dim r0 :: cells0, `Dim r1 :: cells1 ->
        let tr = equate_dim env r0 r1 in
        go (acc #< tr) (D.Env.snoc venv @@ `Dim r0) specs cells0 cells1

      | [], [], [] ->
        Bwd.to_list acc

      | _ ->
        failwith "equate_constr_args: argument mismatch"
    in

    go Emp (D.Env.append empty_env params) (Desc.Constr.specs constr) cells0 cells1

  and equate_neu_ env neu0 neu1 stk =
    match neu0, neu1 with
    | Lvl (_, l0), Lvl (_, l1) ->
      if l0 = l1 then
        (* TODO: twin *)
        Tm.Ix (Env.ix_of_lvl l0 env, `Only), stk
      else
        failwith @@ "equate_neu: expected equal de bruijn levels, but got " ^ string_of_int l0 ^ " and " ^ string_of_int l1
    | Var info0, Var info1 ->
      if info0.name = info1.name && info0.twin = info1.twin && info0.ushift = info1.ushift then
        Tm.Var {name = info0.name; twin = info0.twin; ushift = info0.ushift}, stk
      else
        failwith "global variable name mismatch"
    | Meta meta0, Meta meta1 ->
      if meta0.name = meta1.name && meta0.ushift = meta1.ushift then
        Tm.Meta {name = meta0.name; ushift = meta0.ushift}, stk
      else
        failwith "global variable name mismatch"

    | NHComAtType info0, NHComAtType info1 ->
      let tr, tr' = equate_dir env info0.dir info1.dir in
      let _ = equate_ty env info0.univ info1.univ in
      let ty = equate_neu env info0.ty info1.ty in
      let ty_val = make @@ Up {ty = info0.univ; neu = info0.ty; sys = info0.ty_sys} in
      let cap = equate env ty_val info0.cap info1.cap in
      let sys = equate_comp_sys env ty_val info0.sys info1.sys in
      Tm.HCom {r = tr; r' = tr'; ty = Tm.up ty; cap; sys}, stk

    | NHComAtCap info0, NHComAtCap info1 ->
      let tr, tr' = equate_dir env info0.dir info1.dir in
      let ty = equate_ty env info0.ty info1.ty in
      let cap = equate_neu env info0.cap info1.cap in
      let sys = equate_comp_sys env info0.ty info0.sys info1.sys in
      Tm.HCom {r = tr; r' = tr'; ty; cap = Tm.up cap; sys}, stk

    | NCoe info0, NCoe info1 ->
      let tr, tr' = equate_dir env info0.dir info1.dir in
      let univ = make @@ Univ {kind = `Pre; lvl = `Omega} in
      let bnd = equate_val_abs env univ info0.abs info1.abs in
      let tm = equate_neu env info0.neu info1.neu in
      Tm.Coe {r = tr; r' = tr'; ty = bnd; tm = Tm.up tm}, stk

    | NCoeAtType info0, NCoeAtType info1 ->
      let tr, tr' = equate_dir env info0.dir info1.dir in
      let univ = make @@ Univ {kind = `Pre; lvl = `Omega} in
      let bnd = equate_neu_abs env info0.abs info1.abs in
      let r, _ = Dir.unleash info0.dir in
      let neu_ty_r, sys_ty_r = NeuAbs.inst1 info0.abs r in
      let ty_r = reflect univ neu_ty_r sys_ty_r in
      let tm = equate env ty_r info0.el info1.el in
      Tm.Coe {r = tr; r' = tr'; ty = bnd; tm}, stk

    | Fst neu0, Fst neu1 ->
      equate_neu_ env neu0 neu1 @@ Tm.Fst :: stk

    | Snd neu0, Snd neu1 ->
      equate_neu_ env neu0 neu1 @@ Tm.Snd :: stk

    | FunApp (neu0, nf0), FunApp (neu1, nf1) ->
      let t = equate env nf0.ty nf0.el nf1.el in
      equate_neu_ env neu0 neu1 @@ Tm.FunApp t :: stk

    | ExtApp (neu0, rs0), ExtApp (neu1, rs1) ->
      let ts = equate_dims env rs0 rs1 in
      equate_neu_ env neu0 neu1 @@ Tm.ExtApp ts :: stk

    | Elim elim0, Elim elim1 ->
      if elim0.dlbl = elim1.dlbl then
        let dlbl = elim0.dlbl in
        let data_ty = D.make @@ D.Data {lbl = dlbl; params = elim0.params} in
        let mot =
          let var = generic env data_ty in
          let env' = Env.succ env in
          let vmot0 = inst_clo elim0.mot var in
          let vmot1 = inst_clo elim1.mot var in
          let bdy = equate_ty env' vmot0 vmot1 in
          Tm.B (clo_name elim0.mot, bdy)
        in

        let desc = V.Sig.lookup_datatype dlbl in

        let find_clause clbl clauses =
          try
            snd @@ List.find (fun (clbl', _) -> clbl = clbl') clauses
          with
          | Not_found ->
            failwith "Quote: elim / find_clause"
        in

        let quote_clause (clbl, constr) =
          let clause0 = find_clause clbl elim0.clauses in
          let clause1 = find_clause clbl elim1.clauses in


          let rec go qenv tyenv cells_w_ihs cells specs =
            match specs with
            | (_, `Const ty) :: specs ->
              let vty = V.eval tyenv ty in
              let v = generic qenv vty in
              let tyenv' = D.Env.snoc tyenv @@ `Val v in
              let qenv' = Env.succ qenv in
              go qenv' tyenv' (cells_w_ihs #< (`Val v)) (cells #< (`Val v)) specs

            | (_, `Rec rspec) :: specs ->
              let vty = V.realize_rec_spec ~dlbl ~params:elim0.params rspec in
              let v = generic qenv vty in
              let qenv' = Env.succ qenv in
              let vih = generic qenv' @@ V.inst_clo elim0.mot v in
              let qenv'' = Env.succ qenv' in
              let tyenv' = D.Env.snoc tyenv @@ `Val v in
              go qenv'' tyenv' (cells_w_ihs <>< [`Val v; `Val vih]) (cells #< (`Val v)) specs

            | (nm, `Dim) :: specs ->
              let x = Name.named nm in
              let r = `Atom x in
              let qenv' = Env.abs qenv [x] in
              let tyenv' = D.Env.snoc tyenv @@ `Dim r in
              go qenv' tyenv' (cells_w_ihs #< (`Dim r)) (cells #< (`Dim r)) specs

            | [] ->
              qenv, Bwd.to_list cells_w_ihs, Bwd.to_list cells
          in

          let env', cells_w_ihs, cells = go env (D.Env.append empty_env elim0.params) Emp Emp @@ Desc.Constr.specs constr in

          let bdy0 = inst_nclo clause0 cells_w_ihs in
          let bdy1 = inst_nclo clause1 cells_w_ihs in
          let intro = make_intro ~dlbl ~params:elim0.params ~clbl cells in
          let mot_intro = inst_clo elim0.mot intro in
          let tbdy = equate env' mot_intro bdy0 bdy1 in
          let nms = Bwd.from_list @@ List.map (fun _ -> None) cells_w_ihs in
          clbl, Tm.NB (nms, tbdy)
        in

        let params = equate_data_params env dlbl desc.body elim0.params elim1.params in
        let clauses = List.map quote_clause @@ Desc.constrs desc in
        let frame = Tm.Elim {dlbl; mot; clauses; params} in
        equate_neu_ env elim0.neu elim1.neu @@ frame :: stk
      else
        failwith "Datatype mismatch"

    | VProj vproj0, VProj vproj1 ->
      let x0 = vproj0.x in
      let x1 = vproj1.x in
      let tr = equate_atom env x0 x1 in
      let phi = I.subst `Dim0 x0 in
      let func = equate env vproj0.func.ty vproj0.func.el vproj1.func.el in
      let dom0, cod0 = unleash_pi vproj0.func.ty in
      let dom1, cod1 = unleash_pi vproj1.func.ty in
      let ty0 = equate_ty env dom0 dom1 in
      let dummy = D.make D.FortyTwo in
      let ty1 = equate_ty env (inst_clo cod0 dummy) (inst_clo cod1 dummy) in
      let frame = Tm.VProj {r = tr; ty0; ty1; func} in
      equate_neu_ env vproj0.neu vproj1.neu @@ frame :: stk

    | Cap cap0, Cap cap1 ->
      let tr, tr' = equate_dir env cap0.dir cap1.dir in
      let ty = equate_ty env cap0.ty cap1.ty in
      let univ = make @@ Univ {kind = `Pre; lvl = `Omega} in
      let sys = equate_comp_sys env univ cap0.sys cap1.sys in
      let frame = Tm.Cap {r = tr; r' = tr'; ty; sys} in
      equate_neu_ env cap0.neu cap1.neu @@ frame :: stk

    | RestrictForce neu0, RestrictForce neu1 ->
      equate_neu_ env neu0 neu1 @@ Tm.RestrictForce :: stk

    | _ ->
      let err = UnequalNeu {env; neu0; neu1} in
      raise @@ E err

  and equate_neu env neu0 neu1 =
    equate_neu_ env neu0 neu1 []

  and equate_ty env ty0 ty1 =
    let univ = make @@ Univ {kind = `Pre; lvl = `Omega} in
    equate env univ ty0 ty1


  and equate_val_sys env ty sys0 sys1 =
    try
      List.map2 (equate_val_face env ty) sys0 sys1
    with
    | Invalid_argument _ ->
      failwith "equate_val_sys length mismatch"

  and quote_val_sys env ty sys =
    equate_val_sys env ty sys sys

  and equate_comp_sys env ty sys0 sys1 =
    try
      List.map2 (equate_comp_face env ty) sys0 sys1
    with
    | Invalid_argument _ ->
      failwith "equate_cmop_sys length mismatch"


  and equate_val_face env ty face0 face1 =
    match face0, face1 with
    | Face.True (r0, r'0, v0), Face.True (r1, r'1, v1) ->
      let tr = equate_dim env r0 r1 in
      let tr' = equate_dim env r'0 r'1 in
      let t = equate env ty (Lazy.force v0) (Lazy.force v1) in
      tr, tr', t

    | Face.False (r0, r'0), Face.False (r1, r'1) ->
      let tr = equate_dim env r0 r1 in
      let tr' = equate_dim env r'0 r'1 in
      tr, tr', Tm.forty_two

    | Face.Indet (p0, v0), Face.Indet (p1, v1) ->
      let r, r' = Eq.unleash p0 in
      let phi = I.equate r r' in
      let tr, tr' = equate_eq env p0 p1 in
      let v = equate env (Value.act phi ty) (Lazy.force v0) (Lazy.force v1) in
      tr, tr', v

    | _ -> failwith "equate_val_face"

  and equate_comp_face env ty face0 face1 =
    match face0, face1 with
    | Face.Indet (p0, abs0), Face.Indet (p1, abs1) ->
      let r, r' = Eq.unleash p0 in
      let phi = I.equate r r' in
      let tr, tr' = equate_eq env p0 p1 in
      let bnd = equate_val_abs env (Value.act phi ty) (Lazy.force abs0) (Lazy.force abs1) in
      tr, tr', bnd

  and equate_val_abs env ty abs0 abs1 =
    let x, v0x = Abs.unleash1 abs0 in
    let v1x = Abs.inst1 abs1 @@ `Atom x in
    try
      let envx = Env.abs env [x] in
      let tm = equate envx ty v0x v1x in
      Tm.B (Name.name x, tm)
    with
    | exn ->
      (* Format.eprintf "Failed to equate abs: @[<v>%a@,= %a@]@." pp_abs abs0 pp_abs abs1; *)
      raise exn

  and equate_neu_abs env abs0 abs1 =
    let x, (neu0x, _) = NeuAbs.unleash1 abs0 in
    let neu1x, _ = NeuAbs.inst1 abs1 @@ `Atom x in
    try
      let envx = Env.abs env [x] in
      let cmd = equate_neu envx neu0x neu1x in
      Tm.B (Name.name x, Tm.up cmd)
    with
    | exn ->
      raise exn

  and equate_eq env p0 p1 =
    let r0, r'0 = Eq.unleash p0 in
    let r1, r'1 = Eq.unleash p1 in
    let tr = equate_dim env r0 r1 in
    let tr' = equate_dim env r'0 r'1 in
    tr, tr'

  and equate_eq3 env p0 p1 p2 =
    let r0, r'0 = Eq.unleash p0 in
    let r1, r'1 = Eq.unleash p1 in
    let r2, r'2 = Eq.unleash p2 in
    let tr = equate_dim3 env r0 r1 r2 in
    let tr' = equate_dim3 env r'0 r'1 r'2 in
    tr, tr'

  and equate_dir env p0 p1 =
    let r0, r'0 = Dir.unleash p0 in
    let r1, r'1 = Dir.unleash p1 in
    let tr = equate_dim env r0 r1 in
    let tr' = equate_dim env r'0 r'1 in
    tr, tr'

  and equate_dir3 env p0 p1 p2 =
    let r0, r'0 = Dir.unleash p0 in
    let r1, r'1 = Dir.unleash p1 in
    let r2, r'2 = Dir.unleash p2 in
    let tr = equate_dim3 env r0 r1 r2 in
    let tr' = equate_dim3 env r'0 r'1 r'2 in
    tr, tr'

  and equate_dim env (r : I.t) (r' : I.t) =
    match I.compare r r' with
    | `Same ->
      quote_dim env r
    | _ ->
      (*
         Printexc.print_raw_backtrace stderr (Printexc.get_callstack 20);
         Format.eprintf "@.";
         Format.eprintf "Dimension mismatch: %a <> %a@." I.pp r I.pp r'; *)
      raise @@ E (UnequalDim (r, r'))


  and equate_dim3 env (r : I.t) (r' : I.t) (r'' : I.t) =
    match I.compare r r', I.compare r r'' with
    | `Same, `Same ->
      quote_dim env r
    | _ ->
      (*
         Printexc.print_raw_backtrace stderr (Printexc.get_callstack 20);
         Format.eprintf "@.";
         Format.eprintf "Dimension mismatch: %a <> %a@." I.pp r I.pp r'; *)
      failwith "equate_dim3: dimensions did not match"

  and equate_atom env x y =
    if x = y then
      quote_dim env @@ `Atom x
    else
      failwith "equate_atom: dimensions did not match"

  and equate_dims env rs rs' =
    match rs, rs' with
    | [], [] ->
      []
    | r :: rs, r' :: rs' ->
      let r'' = equate_dim env r r' in
      r'' :: equate_dims env rs rs'
    | _ ->
      failwith "equate_dims: length mismatch"

  and quote_dim env r =
    match r with
    | `Dim0 -> Tm.make Tm.Dim0
    | `Dim1 -> Tm.make Tm.Dim1
    | `Atom x ->
      try
        let ix = Env.ix_of_atom x env in
        Tm.up @@ Tm.ix ix
      with
      | _ ->
        Tm.up @@ Tm.var x

  let equiv env ~ty el0 el1 =
    ignore @@ equate env ty el0 el1

  let equiv_ty env ty0 ty1 =
    ignore @@ equate_ty env ty0 ty1

  let equiv_data_params env dlbl tele cells0 cells1 =
    ignore @@ equate_data_params env dlbl tele cells0 cells1

  let equiv_dim env r0 r1 =
    ignore @@ equate_dim env r0 r1

  let quote_ty env ty =
    equate_ty env ty ty

  let quote_nf env nf =
    equate env nf.ty nf.el nf.el

  let quote_neu env neu =
    equate_neu env neu neu

  let rec subtype env ty0 ty1 =
    fancy_subtype env ty0 [] ty1 []

  and fancy_subtype env ty0 sys0 ty1 sys1 =
    match unleash ty0, unleash ty1 with
    | Pi pi0, Pi pi1 ->
      fancy_subtype env pi1.dom [] pi0.dom [];
      let var = generic env pi0.dom in
      let vcod0 = inst_clo pi0.cod var in
      let vcod1 = inst_clo pi1.cod var in
      let face _r _r' v = apply v var in
      let sys0 = map_sys face sys0 in
      let sys1 = map_sys face sys1 in
      fancy_subtype (Env.succ env) vcod0 sys0 vcod1 sys1

    | Sg sg0, Sg sg1 ->
      let sys00 = map_sys (fun _ _ -> do_fst) sys0 in
      let sys10 = map_sys (fun _ _ -> do_fst) sys1 in
      fancy_subtype env sg0.dom sys00 sg1.dom sys10;
      let var = generic env sg0.dom in
      let vcod0 = inst_clo sg0.cod var in
      let vcod1 = inst_clo sg1.cod var in
      let sys01 = map_sys (fun _ _ -> do_snd) sys0 in
      let sys11 = map_sys (fun _ _ -> do_snd) sys1 in
      fancy_subtype (Env.succ env) vcod0 sys01 vcod1 sys11

    | Ext abs0, Ext abs1 ->
      let xs, (ty0x, sys0x) = ExtAbs.unleash abs0 in
      let xs_fwd = Bwd.to_list xs in
      let rs = Bwd.map (fun x -> `Atom x) xs in
      let ty1x, sys1x = ExtAbs.inst abs1 rs in
      let envxs = Env.abs env xs_fwd in
      let rs_fwd = Bwd.to_list rs in
      let face r r' v =
        let phi = I.equate r r' in
        let rs' = List.map (I.act phi) rs_fwd in
        ext_apply v rs'
      in
      let sys0' = map_sys face sys0 in
      let sys1' = map_sys face sys1 in
      fancy_subtype envxs ty0x (sys0x @ sys0') ty1x (sys1x @ sys1')


    | Univ info0, Univ info1 ->
      if Kind.lte info0.kind info1.kind && Lvl.lte info0.lvl info1.lvl then
        approx_restriction env ty0 ty1 sys0 sys1
      else
        failwith "Universe subtyping error"

    | _ ->
      equiv_ty env ty0 ty1;
      approx_restriction env ty0 ty1 sys0 sys1

  and map_sys f =
    List.map (Face.map f)

  and approx_restriction env ty0 ty1 sys0 sys1 =
    (* A semantic indeterminate of the first type *)
    let gen = generic_constrained env ty0 sys0 in

    let check_face face =
      match face with
      | Face.True (_, _, v) ->
        (* In this case, we need to see that the indeterminate is already equal to the face *)
        begin try equiv env ~ty:ty1 gen (Lazy.force v); true with _ -> false end

      | Face.False _ ->
        (* This one is vacuous *)
        true

      | Face.Indet (p, v) ->
        (* In this case, we check that the semantic indeterminate will become equal to the face under the
           stipulated restriction. *)
        let r, r' = Eq.unleash p in
        let gen_rr' = Value.act (I.equate r r') gen in
        let ty_rr' = Value.act (I.equate r r') ty1 in
        begin try equiv env ~ty:ty_rr' gen_rr' @@ Lazy.force v; true with _ -> false end
    in

    (* This algorithm is very wrong ;-) *)
    let exception Break in
    let n1 = List.length sys1 in
    begin
      try
        for i = 0 to n1 - 1 do
          if check_face (List.nth sys1 i) then () else raise Break
        done
      with
      | Break ->
        (* Format.eprintf "%a <= %a@.@." pp_val_sys sys0 pp_val_sys sys1; *)
        failwith "restriction subtyping"
      | exn ->
        Format.eprintf "Unexpected error in subtyping: %s@." (Printexc.to_string exn);
        raise exn
    end

end

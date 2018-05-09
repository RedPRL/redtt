type atom = Symbol.t
module D = Dim
module Star = DimStar
module Gen = DimGeneric

type can = [`Can]
type neu = [`Neu]

type _ con =
  | Pi : {dom : can value; cod : clo} -> can con
  | Sg : {dom : can value; cod : clo} -> can con
  | Ext : ext_abs -> can con

  | Coe : {dir : Star.t; abs : abs; el : can value} -> can con
  | HCom : {dir : Star.t; ty : can value; cap : can value; sys : comp_sys} -> can con
  | FCom : {dir : Star.t; cap : can value; sys : comp_sys} -> can con

  | Univ : Lvl.t -> can con
  | V : {x : Gen.t; ty0 : can value; ty1 : can value; equiv : can value} -> can con
  | VIn : {x : Gen.t; el0 : can value; el1 : can value} -> can con

  | Lam : clo -> can con
  | ExtLam : abs -> can con
  | Cons : can value * can value -> can con
  | Bool : can con
  | Tt : can con
  | Ff : can con

  | Up : {ty : can value; neu : neu value} -> can con
  | Lvl : int -> neu con
  | FunApp : neu value * can value -> neu con
  | ExtApp : neu value * ext_sys * D.t -> neu con
  | Car : neu value -> neu con
  | Cdr : neu value -> neu con
  | VProj : {x : Gen.t; ty1 : can value; neu : neu value; func : can value} -> neu con

and ('x, 'a) face = ('x, 'a) Face.face

and 'a with_env = {tm : 'a; rho : env}
and cfg = Tm.chk Tm.t with_env node
and clo = Tm.chk Tm.t Tm.bnd with_env node
and env_el = Val of can value | Atom of atom
and env = env_el list

and abs = can value Abstraction.abs
and ext_abs = (can value * ext_sys) Abstraction.abs
and rigid_abs_face = ([`Rigid], abs) face
and val_face = ([`Any], can value) face
and rigid_val_face = ([`Rigid], can value) face

and comp_sys = rigid_abs_face list
and ext_sys = val_face list
and box_sys = rigid_val_face list
and cap_sys = rigid_abs_face list

and 'a node = {inner : 'a; action : D.action}
and 'a value = 'a con node ref

type _ step =
  | Ret : 'a con -> 'a step
  | Step : can value -> 'a step

let ret v = Ret v
let step v = Step v

module type Sort = Sort.S

module Val =
struct
  let into : type a. a con -> a value =
    fun inner ->
      ref @@ {inner; action = D.idn}

  let from_step (step : can step) : can value =
    match step with
    | Ret con -> into con
    | Step t -> t

  let act : type a. D.action -> a value -> a value =
    fun phi node ->
      ref @@ {!node with action = D.cmp phi !node.action}
end

module CanVal : Sort with type t = can value with type 'a m = 'a =
struct
  include Val
  type 'a m = 'a
  type t = can value
end

module Abs = Abstraction.M (CanVal)

module ValFace = Face.M (CanVal)
module AbsFace = Face.M (Abs)

module Clo : Sort with type t = clo with type 'a m = 'a =
struct
  type t = clo
  type 'a m = 'a

  let act phi clo =
    {clo with action = D.cmp phi clo.action}
end

module CompSys :
sig
  include Sort
    with type t = comp_sys
    with type 'a m = [`Ok of comp_sys | `Proj of abs]
end =
struct
  type t = comp_sys
  type 'a m = [`Ok of comp_sys | `Proj of abs]

  exception Proj of abs

  let rec act_aux phi (sys : t) =
    match sys with
    | [] -> []
    | face :: sys ->
      match AbsFace.act phi face with
      | Face.True (_, _, abs) ->
        raise @@ Proj abs
      | Face.False p ->
        Face.False p :: act_aux phi sys
      | Face.Indet (p, t) ->
        Face.Indet (p, t) :: act_aux phi sys

  let act phi sys =
    try `Ok (act_aux phi sys)
    with
    | Proj abs ->
      `Proj abs
end

module ExtSys :
sig
  include Sort
    with type t = ext_sys
    with type 'a m = 'a
end =
struct
  type t = ext_sys
  type 'a m = 'a

  let act phi =
    List.map (ValFace.act phi)
end

module ExtAbs = Abstraction.M (Sort.Prod (CanVal) (ExtSys))

let set_tm tm cfg =
  {cfg with inner = {cfg.inner with tm}}

exception ProjAbs of abs
exception ProjVal of can value


let eval_dim (cfg : cfg) : D.t =
  match Tm.out cfg.inner.tm with
  | Tm.Dim0 ->
    D.dim0
  | Tm.Dim1 ->
    D.dim1
  | Tm.Var i ->
    begin
      match List.nth cfg.inner.rho i with
      | Atom x ->
        D.named x
      (* D.act cfg.action @@ D.named x *)
      (* TODO: should I do this here? I think not, but I'm not sure. *)
      | _ ->
        failwith "eval_dim: expected atom in environment"
    end
  | _ ->
    failwith "eval_dim"



let rec act : type a. D.action -> a con -> a step =
  fun phi (con : a con) ->
    match con with
    | Pi info ->
      let dom = Val.act phi info.dom in
      let cod = Clo.act phi info.cod in
      ret @@ Pi {dom; cod}

    | Sg info ->
      let dom = Val.act phi info.dom in
      let cod = Clo.act phi info.cod in
      ret @@ Sg {dom; cod}

    | Ext abs ->
      let abs' = ExtAbs.act phi abs in
      ret @@ Ext abs'

    | Coe info ->
      make_coe
        (Star.act phi info.dir)
        (Abs.act phi info.abs)
        (Val.act phi info.el)

    | HCom info ->
      make_hcom
        (Star.act phi info.dir)
        (Val.act phi info.ty)
        (Val.act phi info.cap)
        (CompSys.act phi info.sys)

    | FCom info ->
      make_fcom
        (Star.act phi info.dir)
        (Val.act phi info.cap)
        (CompSys.act phi info.sys)

    | V info ->
      make_v
        (Gen.act phi info.x)
        (Val.act phi info.ty0)
        (Val.act phi info.ty1)
        (Val.act phi info.equiv)

    | VIn info ->
      make_vin
        (Gen.act phi info.x)
        (Val.act phi info.el0)
        (Val.act phi info.el1)

    | VProj info ->
      step @@
      let mx = Gen.act phi info.x in
      let el = Val.act phi @@ Val.into @@ Up {ty = info.ty1; neu = info.neu} in
      let func = Val.act phi info.func in
      vproj mx el func

    | Univ _ ->
      ret con

    | Bool ->
      ret con

    | Tt ->
      ret con

    | Ff ->
      ret con

    | Lam clo ->
      ret @@ Lam (Clo.act phi clo)

    | ExtLam abs ->
      ret @@ ExtLam (Abs.act phi abs)

    | Cons (v0, v1) ->
      ret @@ Cons (Val.act phi v0, Val.act phi v1)

    | FunApp (neu, arg) ->
      ret @@ FunApp (Val.act phi neu, Val.act phi arg)

    | ExtApp (neu, sys, r) ->
      let sys' = ExtSys.act phi sys in
      begin
        match force_ext_sys sys' with
        | `Rigid _ ->
          let neu' = Val.act phi neu in
          let r' = Dim.act phi r in
          ret @@ ExtApp (neu', sys', r')
        | `Proj v ->
          step v
      end

    | Car neu ->
      ret @@ Car (Val.act phi neu)

    | Cdr neu ->
      ret @@ Cdr (Val.act phi neu)

    | Lvl _ ->
      ret con

    | Up info ->
      let ty = Val.act phi info.ty in
      let neu = Val.act phi info.neu in
      ret @@ Up {ty; neu}

and force_abs_face face =
  match face with
  | Face.True (_, _, abs) ->
    raise @@ ProjAbs abs
  | Face.False xi ->
    Face.False xi
  | Face.Indet (xi, abs) ->
    Face.Indet (xi, abs)

and force_ext_face (face : val_face) =
  match face with
  | Face.True (_, _, v) ->
    raise @@ ProjVal v
  | Face.False xi ->
    Face.False xi
  | Face.Indet (xi, v) ->
    Face.Indet (xi, v)

and force_ext_sys sys =
  try
    `Rigid (List.map force_ext_face sys)
  with
  | ProjVal v ->
    `Proj v

and force_abs_sys sys =
  try
    `Ok (List.map force_abs_face sys)
  with
  | ProjAbs abs ->
    `Proj abs

and unleash_can : can value -> can con =
  fun node ->
    match act !node.action !node.inner with
    | Ret con ->
      node := {inner = con; action = D.idn};
      con
    | Step t ->
      let con = unleash_can t in
      node := {inner = con; action = D.idn};
      con

and unleash_neu : neu value -> [`Neu of neu con | `Step of can value] =
  fun node ->
    match act !node.action !node.inner with
    | Ret con ->
      node := {inner = con; action = D.idn};
      `Neu con
    | Step t ->
      `Step t


and make_v mgen ty0 ty1 equiv : can step =
  match mgen with
  | `Ok x ->
    ret @@ V {x; ty0; ty1; equiv}
  | `Const `Dim0 ->
    step ty0
  | `Const `Dim1 ->
    step ty1

and make_vin mgen el0 el1 : can step =
  match mgen with
  | `Ok x ->
    ret @@ VIn {x; el0; el1}
  | `Const `Dim0 ->
    step el0
  | `Const `Dim1 ->
    step el0

and make_coe mdir abs el : can step =
  match mdir with
  | `Ok dir ->
    rigid_coe dir abs el
  | `Same _ ->
    step el

and make_hcom mdir ty cap msys : can step =
  match mdir with
  | `Ok dir ->
    begin
      match msys with
      | `Ok sys ->
        rigid_hcom dir ty cap sys
      | `Proj abs ->
        let _, r' = Star.unleash dir in
        let x, el = Abs.unleash abs in
        step @@ Val.act (D.subst r' x) el
    end
  | `Same _ ->
    step cap

and make_fcom mdir cap msys : can step =
  match mdir with
  | `Ok dir ->
    begin
      match msys with
      | `Ok sys ->
        ret @@ FCom {dir; cap; sys}
      | `Proj abs ->
        let _, r' = Star.unleash dir in
        let x, el = Abs.unleash abs in
        step @@ Val.act (D.subst r' x) el
    end
  | `Same _ ->
    step cap

and rigid_coe dir abs el : can step =
  let x, tyx = Abs.unleash abs in
  match unleash_can tyx with
  | (Pi _ | Sg _ ) ->
    ret @@ Coe {dir; abs; el}

  | (Bool | Univ _) ->
    step el

  | FCom _info ->
    failwith "Coe in fcom, taste it!!"

  | V info ->
    begin
      let r, r' = Star.unleash dir in
      let xty1 = Abs.bind x info.ty1 in
      match Gen.make r with
      | `Const `Dim0 ->
        let el1 =
          Val.from_step @@
          rigid_coe dir xty1 @@
          apply (car @@ Val.act (D.subst D.dim0 x) info.equiv) el
        in
        make_vin (Gen.make r') el el1

      | `Const `Dim1 ->
        let coe1r'el = Val.from_step @@ rigid_coe dir xty1 el in
        let el0 = car @@ apply (cdr @@ Val.act (D.subst r' x) info.equiv) coe1r'el in
        let el1 =
          Val.from_step @@
          let ty1r' = Val.act (D.subst r' x) info.ty1 in
          let cap = coe1r'el in
          let sys =
            force_abs_sys @@
            let face0 =
              AbsFace.make r' D.dim0 @@
              let y = Symbol.fresh () in
              Abs.bind y @@ ext_apply (cdr el0) @@ D.named y
            in
            let face1 = AbsFace.make r' D.dim1 @@ Abs.const coe1r'el in
            [face0; face1]
          in
          make_hcom (Star.make D.dim1 D.dim0) ty1r' cap sys
        in
        make_vin (Gen.make r') (car el0) el1

      | `Ok _ ->
        begin
          match D.compare (Gen.unleash info.x) (D.named x) with
          | D.Same ->
            failwith "This is the hard one"

          | _ ->
            let xty0 = Abs.bind x info.ty0 in
            let el0 = Val.from_step @@ rigid_coe dir xty0 el in
            let el1 =
              let cap = rigid_vproj info.x el @@ car @@ Val.act (Dim.subst r x) info.equiv in
              let sys =
                let face0 =
                  AbsFace.gen_const info.x `Dim0 @@
                  Abs.bind x @@ apply (car info.equiv) @@
                  Val.from_step @@ make_coe (Star.make r (D.named x)) xty0 el
                in
                let face1 =
                  AbsFace.gen_const info.x `Dim1 @@
                  Abs.bind x @@
                  Val.from_step @@ make_coe (Star.make r (D.named x)) xty1 el
                in
                [face0; face1]
              in
              Val.from_step @@ rigid_com dir xty1 cap sys
            in
            ret @@ VIn {x = info.x; el0; el1}
        end


    end

  | _ ->
    failwith "TODO: rigid_coe"

and rigid_hcom dir ty cap sys : can step =
  match unleash_can ty with
  | Pi _ ->
    ret @@ HCom {dir; ty; cap; sys}

  | Bool ->
    step cap

  | Univ _ ->
    ret @@ FCom {dir; cap; sys}

  | FCom _info ->
    failwith "hcom in fcom, taste it!!"

  | V _info ->
    failwith "hcom in V, taste it!!!"

  | _ ->
    failwith "TODO"

and rigid_com dir abs cap (sys : comp_sys) : can step =
  let _, r' = Star.unleash dir in
  let ty = Abs.inst abs r' in
  let capcoe = Val.from_step @@ rigid_coe dir abs cap in
  let syscoe : comp_sys =
    let face =
      Face.map @@ fun ri r'i absi ->
      let phi = D.equate ri r'i in
      let yi, vi = Abs.unleash absi in
      let y2r' = Star.make (D.named yi) (D.act phi r') in
      Abs.bind yi @@ Val.from_step @@
      make_coe y2r' abs vi
    in
    List.map face sys
  in
  rigid_hcom dir ty capcoe syscoe

and eval (cfg : cfg) : can value =
  match Tm.out cfg.inner.tm with
  | Tm.Var i ->
    begin
      match List.nth cfg.inner.rho i with
      | Val v -> v
      | _ -> failwith "Expected value in environment"
    end

  | Tm.Pi (dom, cod) ->
    let dom = eval @@ set_tm dom cfg in
    let cod = set_tm cod cfg in
    Val.into @@ Pi {dom; cod}

  | Tm.Sg (dom, cod) ->
    let dom = eval @@ set_tm dom cfg in
    let cod = set_tm cod cfg in
    Val.into @@ Sg {dom; cod}

  | Tm.Ext bnd ->
    let abs = eval_ext_abs @@ set_tm bnd cfg in
    Val.into @@ Ext abs

  | Tm.Lam bnd ->
    Val.into @@ Lam (set_tm bnd cfg)

  | Tm.ExtLam bnd ->
    let abs = eval_abs @@ set_tm bnd cfg in
    Val.into @@ ExtLam abs

  | Tm.Cons (t0, t1) ->
    let v0 = eval @@ set_tm t0 cfg in
    let v1 = eval @@ set_tm t1 cfg in
    Val.into @@ Cons (v0, v1)

  | Tm.Coe info ->
    Val.from_step @@
    let r = eval_dim @@ set_tm info.r cfg in
    let r' = eval_dim @@ set_tm info.r' cfg in
    let dir = Star.make r r' in
    let abs = eval_abs @@ set_tm info.ty cfg in
    let el = eval @@ set_tm info.tm cfg in
    make_coe dir abs el

  | Tm.HCom info ->
    Val.from_step @@
    let r = eval_dim @@ set_tm info.r cfg in
    let r' = eval_dim @@ set_tm info.r' cfg in
    let dir = Star.make r r' in
    let ty = eval @@ set_tm info.ty cfg in
    let cap = eval @@ set_tm info.cap cfg in
    let sys = eval_abs_sys @@ set_tm info.sys cfg in
    make_hcom dir ty cap sys

  | Tm.FCom info ->
    Val.from_step @@
    let r = eval_dim @@ set_tm info.r cfg in
    let r' = eval_dim @@ set_tm info.r' cfg in
    let dir = Star.make r r' in
    let cap = eval @@ set_tm info.cap cfg in
    let sys = eval_abs_sys @@ set_tm info.sys cfg in
    make_fcom dir cap sys

  | Tm.FunApp (t0, t1) ->
    let v0 = eval @@ set_tm t0 cfg in
    let v1 = eval @@ set_tm t1 cfg in
    apply v0 v1

  | Tm.ExtApp (t, tr) ->
    let v = eval @@ set_tm t cfg in
    let r = eval_dim @@ set_tm tr cfg in
    ext_apply v r

  | Tm.Car t ->
    car @@ eval @@ set_tm t cfg

  | Tm.Cdr t ->
    cdr @@ eval @@ set_tm t cfg

  | Tm.Univ lvl ->
    Val.into @@ Univ lvl

  | Tm.Bool ->
    Val.into Bool

  | Tm.Tt ->
    Val.into Tt

  | Tm.Ff ->
    Val.into Ff

  | _ ->
    failwith ""

and eval_abs_face cfg =
  let tr, tr', obnd = cfg.inner.tm in
  let r = eval_dim @@ set_tm tr cfg in
  let r' = eval_dim @@ set_tm tr' cfg in
  match Star.make r r' with
  | `Ok xi ->
    begin
      match D.compare r r' with
      | D.Apart ->
        Face.False xi
      | _ ->
        let bnd = Option.get_exn obnd in
        let abs =
          eval_abs
            {inner = {cfg.inner with tm = bnd};
             action = D.cmp (D.equate r r') cfg.action}
        in
        Face.Indet (xi, abs)
    end
  | `Same _ ->
    let bnd = Option.get_exn obnd in
    let abs = eval_abs @@ set_tm bnd cfg in
    Face.True (r, r', abs)

and eval_abs_sys cfg =
  try
    let sys =
      List.map
        (fun x -> force_abs_face @@ eval_abs_face @@ set_tm x cfg)
        cfg.inner.tm
    in `Ok sys
  with
  | ProjAbs abs ->
    `Proj abs

and eval_ext_face cfg : val_face =
  let tr, tr', otm = cfg.inner.tm in
  let r = eval_dim @@ set_tm tr cfg in
  let r' = eval_dim @@ set_tm tr' cfg in
  match Star.make r r' with
  | `Ok xi ->
    begin
      match D.compare r r' with
      | D.Apart ->
        Face.False xi
      | _ ->
        let tm = Option.get_exn otm in
        let el =
          eval
            {inner = {cfg.inner with tm};
             action = D.cmp (D.equate r r') cfg.action}
        in
        Face.Indet (xi, el)
    end
  | `Same _ ->
    let tm = Option.get_exn otm in
    let el = eval @@ set_tm tm cfg in
    Face.True (r, r', el)

and eval_ext_sys (sys : Tm.chk Tm.t Tm.system with_env node) : ext_sys =
  List.map
    (fun x -> eval_ext_face @@ set_tm x sys)
    sys.inner.tm

and eval_abs cfg =
  let Tm.B (_, tm) = cfg.inner.tm in
  let x = Symbol.fresh () in
  let rho = Atom x :: cfg.inner.rho in
  Abs.bind x @@ eval {cfg with inner = {tm; rho}}

and eval_ext_abs cfg =
  let Tm.B (_, (tm, sys)) = cfg.inner.tm in
  let x = Symbol.fresh () in
  let rho = Atom x :: cfg.inner.rho in
  ExtAbs.bind x (eval {cfg with inner = {tm; rho}}, eval_ext_sys {cfg with inner = {tm = sys; rho}})

and unleash_pi v =
  match unleash_can v with
  | Pi {dom; cod} -> dom, cod
  | _ -> failwith "unleash_pi"

and unleash_sg v =
  match unleash_can v with
  | Sg {dom; cod} -> dom, cod
  | _ -> failwith "unleash_sg"

and unleash_ext v r =
  match unleash_can v with
  | Ext abs ->
    ExtAbs.inst abs r
  | _ ->
    failwith "unleash_ext"

and unleash_v v =
  match unleash_can v with
  | V {x; ty0; ty1; equiv} ->
    x, ty0, ty1, equiv
  | _ ->
    failwith "unleash_v"

and apply vfun varg =
  match unleash_can vfun with
  | Lam clo ->
    inst_clo clo varg

  | Up info ->
    begin
      match unleash_neu info.neu with
      | `Step el ->
        apply el varg
      | `Neu neu ->
        let _, cod = unleash_pi info.ty in
        let cod' = inst_clo cod varg in
        let app = Val.into @@ FunApp (Val.into neu, varg) in
        Val.into @@ Up {ty = cod'; neu = app}
    end

  | Coe info ->
    Val.from_step @@
    let r, r' = Star.unleash info.dir in
    let x, tyx = Abs.unleash info.abs in
    let domx, codx = unleash_pi tyx in
    let abs =
      Abs.bind x @@
      inst_clo codx @@
      Val.from_step @@
      make_coe
        (Star.make r' (D.named x))
        (Abs.bind x domx)
        varg
    in
    let el =
      apply info.el @@
      Val.from_step @@
      make_coe
        (Star.make r' r)
        (Abs.bind x domx)
        varg
    in
    rigid_coe info.dir abs el

  | HCom info ->
    let _, cod = unleash_pi info.ty in
    let ty = inst_clo cod varg in
    let cap = apply info.cap varg in
    let app_face =
      Face.map @@ fun r r' abs ->
      let x, v = Abs.unleash abs in
      Abs.bind x @@ apply v (Val.act (D.equate r r') v)
    in
    let sys = List.map app_face info.sys in
    Val.from_step @@
    rigid_hcom info.dir ty cap sys

  | _ ->
    failwith "apply"

and ext_apply vext s =
  match unleash_can vext with
  | ExtLam abs ->
    Abs.inst abs s

  | Up info ->
    begin
      match unleash_neu info.neu with
      | `Step el ->
        ext_apply el s
      | `Neu neu ->
        let tyr, sysr = unleash_ext info.ty s in
        begin
          match force_ext_sys sysr with
          | `Rigid _ ->
            let app = Val.into @@ ExtApp (Val.into neu, sysr, s) in
            Val.into @@ Up {ty = tyr; neu = app}
          | `Proj v ->
            v
        end
    end

  | Coe info ->
    let y, ext_y = Abs.unleash info.abs in
    let ty_s, sys_s = unleash_ext ext_y s in
    let forall_y_sys_s =
      let filter_face face =
        match Face.forall y face with
        | `Keep -> true
        | `Delete -> false
      in
      List.filter filter_face sys_s
    in
    begin
      match force_ext_sys forall_y_sys_s with
      | `Proj v ->
        v

      | `Rigid rsys ->
        let correction =
          let face = Face.map @@ fun _ _ v -> Abs.bind y v in
          List.map face rsys
        in
        let abs = Abs.bind y ty_s in
        let cap = ext_apply info.el s in
        Val.from_step @@
        rigid_com info.dir abs cap correction
    end

  | HCom info ->
    let ty_s, sys_s = unleash_ext info.ty s in
    begin
      match force_ext_sys sys_s with
      | `Proj v ->
        v
      | `Rigid boundary_sys ->
        Val.from_step @@
        let cap = ext_apply info.cap s in
        let correction_sys =
          let face = Face.map @@ fun _ _ v -> Abs.const v in
          List.map face boundary_sys
        in
        rigid_hcom info.dir ty_s cap @@ correction_sys @ info.sys
    end

  | _ ->
    failwith "ext_apply"


and vproj mgen el func : can value =
  match mgen with
  | `Ok x ->
    rigid_vproj x el func
  | `Const `Dim0 ->
    apply func el
  | `Const `Dim1 ->
    el

and rigid_vproj x el func : can value =
  match unleash_can el with
  | VIn info ->
    (* Invariant: info.x == x, not well-typed otherwise *)
    info.el1
  | Up up ->
    let _, _, ty1, _ = unleash_v up.ty in
    let neu = Val.into @@ VProj {x; ty1; neu = up.neu; func} in
    Val.into @@ Up {ty = ty1; neu}
  | _ -> failwith "vproj"

and car v =
  match unleash_can v with
  | Cons (v0, _) ->
    v0

  | Up info ->
    begin
      match unleash_neu info.neu with
      | `Step el ->
        car el
      | `Neu neu ->
        let dom, _ = unleash_sg info.ty in
        let neu = Val.into neu in
        Val.into @@ Up {ty = dom; neu = Val.into @@ Car neu}
    end

  | Coe info ->
    Val.from_step @@
    let x, tyx = Abs.unleash info.abs in
    let domx, _ = unleash_sg tyx in
    let abs = Abs.bind x domx in
    let el = car info.el in
    rigid_coe info.dir abs el

  | HCom info ->
    Val.from_step @@
    let dom, _ = unleash_sg info.ty in
    let cap = car info.cap in
    let face =
      Face.map @@ fun _ _ abs ->
      let y, v = Abs.unleash abs in
      Abs.bind y @@ car v
    in
    let sys = List.map face info.sys in
    rigid_hcom info.dir dom cap sys

  | _ ->
    failwith "car"

and cdr v =
  match unleash_can v with
  | Cons (_, v1) ->
    v1

  | Coe info ->
    Val.from_step @@
    let abs =
      let x, tyx = Abs.unleash info.abs in
      let domx, codx = unleash_sg tyx in
      let r, _ = Star.unleash info.dir in
      let coerx =
        Val.from_step @@
        make_coe
          (Star.make r (D.named x))
          (Abs.bind x domx)
          (car info.el)
      in
      Abs.bind x @@ inst_clo codx coerx
    in
    let el = cdr info.el in
    rigid_coe info.dir abs el

  | HCom info ->
    Val.from_step @@
    let abs =
      let r, _ = Star.unleash info.dir in
      let dom, cod = unleash_sg info.ty in
      let z = Symbol.fresh () in
      let sys =
        let face =
          Face.map @@ fun _ _ absi ->
          let yi, vi = Abs.unleash absi in
          Abs.bind yi @@ car vi
        in
        `Ok (List.map face info.sys)
      in
      let hcom =
        Val.from_step @@
        make_hcom
          (Star.make r (D.named z))
          dom
          (car info.cap)
          sys
      in
      Abs.bind z @@ inst_clo cod hcom
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

  | _ -> failwith "TODO: cdr"

and inst_clo clo varg =
  let Tm.B (_, tm) = clo.inner.tm in
  eval {clo with inner = {tm; rho = Val varg :: clo.inner.rho}}

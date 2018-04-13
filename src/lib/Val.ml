type can = [`Can]
type neu = [`Neu]

type 'a tube = DimVal.t * DimVal.t * 'a option
type 'a system = 'a tube list

type rel = DimRel.t


type _ f =
  | Lvl : int -> neu f

  | Up : can t * neu t -> can f

  | Pi : tclo * bclo -> can f
  | Sg : tclo * bclo -> can f
  | Univ : Lvl.t -> can f
  | Interval : Cube.t -> can f

  | Dim0 : can f
  | Dim1 : can f

  | Lam : bclo -> can f
  | Cons : tclo * tclo -> can f

  | Coe : {tag : Cube.t; dim0 : can t; dim1 : can t; ty : bclo; tm : can t} -> can f
  | HCom : {tag : Cube.t; dim0 : can t; dim1 : can t; ty : tclo; cap : can t; sys : bclo system} -> can f

  | App : neu t * can t -> neu f
  | Car : neu t -> neu f
  | Cdr : neu t -> neu f

and 'a t = { con : 'a f }
and env = { vals : can t list; rel : DimRel.t }

and 'a clo = { foc : 'a; thin : Thin.t; env : env; stk : stk }
and tclo = Tm.chk Tm.t clo
and bclo = Tm.chk Tm.t Tm.bnd clo

and frm =
  | KApply of can t
  | KCar
  | KCdr
  | KComTubeCoe of {tag : Cube.t; dim1 : can t; ty : bclo; tube : bclo}
  | KPiDom
  | KPiCodCoe of {tag : Cube.t; dim1 : can t; dom : bclo; arg : can t}
  | KSgDom
  | KSgCodCoe of {tag : Cube.t; dim0 : can t; dom : bclo; arg : can t}
  | KSgCodHCom of {tag : Cube.t; dim0 : can t; dom : tclo; cap : can t; sys : bclo system}

and stk = frm list


module Env :
sig
  type el = can t

  type t = env
  val emp : t
  val ext : t -> el -> t

  val lookup : Thin.t -> t -> el
  val thin : Thin.t -> t -> t

  val rel : t -> DimRel.t
  val set_rel : DimRel.t -> t -> t

  include DimRel.S with type t := t
end =
struct
  type el = can t
  type t = env

  let emp =
    {vals = [];
     rel = DimRel.emp}

  let ext env v =
    {vals = v :: env.vals;
     rel = env.rel}

  let lookup th env =
    Thin.proj th env.vals

  let thin th env =
    {env with vals = Thin.act th env.vals}

  exception Inconsistent = DimRel.Inconsistent

  let restrict_exn env d0 d1 =
    let rel = DimRel.restrict_exn env.rel d0 d1 in
    {env with rel = rel}

  let compare_dim env =
    DimRel.compare_dim env.rel

  let rel env = env.rel
  let set_rel rl env = {env with rel = rl}
end

let into vf =
  {con = vf}


let embed_dimval dv =
  into @@
  match dv with
  | DimVal.Dim0 -> Dim0
  | DimVal.Dim1 -> Dim1
  | DimVal.Lvl (tag, i) -> Up (into @@ Interval tag, into @@ Lvl i)

let out : type a. a t -> a f =
  fun node -> node.con


let project_dimval (type a) (v : a t) =
  match out v with
  | Dim0 -> DimVal.Dim0
  | Dim1 -> DimVal.Dim1
  | Up (vty, vneu) ->
    begin
      match out vty, out vneu with
      | Interval tag, Lvl i -> DimVal.Lvl (tag, i)
      | _ -> failwith "project_dimval/Up"
    end
  | _ -> failwith "project_dimval"

let (<:) tm rho : 'a =
  { foc = tm
  ; env = rho
  ; thin = Thin.id
  ; stk = []
  }


let map_tubes f =
  List.map @@ fun (vd0, vd1, vbnd) ->
  (vd0, vd1, Option.map f vbnd)

let clo_frame : frm -> tclo -> tclo =
  fun frm node ->
    { node with stk = frm :: node.stk}

let bclo_frame : frm -> bclo -> bclo =
  fun frm node ->
    { node with stk = frm :: node.stk }


let coe ~rel ~tag ~dim0 ~dim1 ~ty ~tm =
  match DimRel.compare_dim rel (project_dimval dim0) (project_dimval dim1) with
  | DimVal.Same -> tm
  | _ -> into @@ Coe {tag; dim0; dim1; ty; tm}




let out_pi v =
  match out v with
  | Pi (dom, cod) -> dom, cod
  | _ -> failwith "out_pi"

let out_sg v =
  match out v with
  | Sg (dom, cod) -> dom, cod
  | _ -> failwith "out_sg"


let rec eval : type a. env -> a Tm.t -> can t =
  fun rho tm ->
    match Tm.out tm with
    | Tm.Var i ->
      Env.lookup i rho

    | Tm.Pi (dom, cod) ->
      into @@ Pi (dom <: rho, cod <: rho)

    | Tm.Sg (dom, cod) ->
      into @@ Sg (dom <: rho, cod <: rho)

    | Tm.Lam bdy ->
      into @@ Lam (bdy <: rho)

    | Tm.Cons (t0, t1) ->
      into @@ Cons (t0 <: rho, t1 <: rho)

    | Tm.Coe info ->
      let vd0 = eval rho info.dim0 in
      let vd1 = eval rho info.dim1 in
      let vtm = eval rho info.tm in
      coe ~rel:(Env.rel rho) ~tag:info.tag ~dim0:vd0 ~dim1:vd1 ~ty:(info.ty <: rho) ~tm:vtm

    | Tm.HCom info ->
      let vd0 = eval rho info.dim0 in
      let vd1 = eval rho info.dim1 in
      let vcap = eval rho info.cap in
      let vsys = eval_bsys rho info.sys in
      hcom ~rel:(Env.rel rho) ~tag:info.tag ~dim0:vd0 ~dim1:vd1 ~ty:(info.ty <: rho) ~cap:vcap ~sys:vsys

    | Tm.Com info ->
      let vd0 = eval rho info.dim0 in
      let vd1 = eval rho info.dim1 in
      let vcap = eval rho info.cap in
      let vsys = eval_bsys rho info.sys in
      com ~rel:(Env.rel rho) ~tag:info.tag ~dim0:vd0 ~dim1:vd1 ~ty:(info.ty <: rho) ~cap:vcap ~sys:vsys

    | Tm.Univ lvl ->
      into @@ Univ lvl

    | Tm.Interval tag ->
      into @@ Interval tag

    | Tm.Dim0 ->
      into Dim0

    | Tm.Dim1 ->
      into Dim1

    | Tm.Car t ->
      car (Env.rel rho) @@ eval rho t

    | Tm.Cdr t ->
      cdr (Env.rel rho) @@ eval rho t

    | Tm.App (t1, t2) ->
      apply (Env.rel rho) (eval rho t1) (eval rho t2)

    | Tm.Down t ->
      eval rho t.tm

    | Tm.Up t ->
      eval rho t

and project_bsys ~rel ~dim1 ~sys =
  let rec go tubes =
    match tubes with
    | [] -> `Ret sys
    | (vd0, vd1, obclo) :: sys ->
      match DimRel.compare_dim rel vd0 vd1, obclo with
      | DimVal.Same, Some bclo ->
        `Throw (inst_bclo bclo dim1)
      | DimVal.Same, None ->
        failwith "project_bsys: expected Some"
      | _, _ -> go tubes
  in
  go sys

and hcom ~rel ~tag ~dim0 ~dim1 ~ty ~cap ~sys =
  match DimRel.compare_dim rel (project_dimval dim0) (project_dimval dim1) with
  | DimVal.Same -> cap
  | _ ->
    match project_bsys ~rel ~dim1 ~sys with
    | `Ret sys -> into @@ HCom {tag; dim0; dim1; ty; cap; sys}
    | `Throw v -> v

and com ~rel ~tag ~dim0 ~dim1 ~ty ~cap ~sys =
  let vcap' = coe ~rel ~tag ~dim0 ~dim1 ~ty ~tm:cap in
  let Tm.B tm = ty.foc in
  let ty1 = {ty with foc = tm; env = Env.ext ty.env dim1} in
  let tube bclo' = bclo_frame (KComTubeCoe {tag; dim1 = dim1; ty = ty; tube = bclo'}) ty in
  let vsys' = map_tubes tube sys in
  hcom ~rel ~tag ~dim0 ~dim1 ~ty:ty1 ~cap:vcap' ~sys:vsys'


and eval_sys rho sys =
  List.map (eval_tube rho) sys

and eval_bsys rho bsys =
  List.map (eval_btube rho) bsys

and eval_tube rho (t0, t1, otm) =
  let vd0 = project_dimval @@ eval rho t0 in
  let vd1 = project_dimval @@ eval rho t1 in
  try
    let rho' = Env.restrict_exn rho vd0 vd1 in
    let tm = Option.get_exn otm in
    (vd0, vd1, Some (tm <: rho'))
  with
  | Env.Inconsistent -> (vd0, vd1, None)

and eval_btube rho (t0, t1, obnd) =
  let vd0 = project_dimval @@ eval rho t0 in
  let vd1 = project_dimval @@ eval rho t1 in
  try
    let rho' = Env.restrict_exn rho vd0 vd1 in
    let bnd = Option.get_exn obnd in
    (vd0, vd1, Some (bnd <: rho'))
  with
  | Env.Inconsistent -> (vd0, vd1, None)

and apply rel vfun varg =
  match out vfun with
  | Lam bclo ->
    inst_bclo bclo varg

  | Up (vty, vneu) ->
    let dom, cod = out_pi vty in
    let vcod = inst_bclo cod varg in
    reflect rel vcod @@ into @@ App (vneu, varg)

  | Coe info ->
    let dom = bclo_frame KPiDom info.ty in
    let cod = bclo_frame (KPiCodCoe {tag = info.tag; dim1 = info.dim1; dom = dom; arg = varg}) info.ty in
    let varg' = coe ~rel ~tag:info.tag ~dim0:info.dim1 ~dim1:info.dim0 ~ty:dom ~tm:varg in
    coe ~rel ~tag:info.tag ~dim0:info.dim0 ~dim1:info.dim1 ~ty:cod ~tm:(apply rel info.tm varg')

  | HCom info ->
    let dom, cod = out_pi @@ eval_clo info.ty in
    let Tm.B tm = cod.foc in
    let cod' = {cod with foc = tm; env = Env.ext cod.env varg} in
    let vcap' = apply rel info.cap varg in
    let vsys' = map_tubes (bclo_frame (KApply varg)) info.sys in
    hcom ~rel ~tag:info.tag ~dim0:info.dim0 ~dim1:info.dim1 ~ty:cod' ~cap:vcap' ~sys:vsys'

  | _ -> failwith "apply"

and car rel v =
  match out v with
  | Cons (clo, _) ->
    eval_clo clo

  | Up (vty, vneu) ->
    let dom, _ = out_sg vty in
    let vdom = eval_clo dom in
    reflect rel vdom @@ into @@ Car vneu

  | Coe info ->
    let dom = bclo_frame KSgDom info.ty in
    let vcar = car rel v in
    coe ~rel:rel ~tag:info.tag ~dim0:info.dim0 ~dim1:info.dim1 ~ty:dom ~tm:vcar

  | HCom info ->
    let dom, _ = out_sg @@ eval_clo info.ty in
    let vcap' = car rel info.cap in
    let vsys' = map_tubes (bclo_frame KCar) info.sys in
    hcom ~rel ~tag:info.tag ~dim0:info.dim0 ~dim1:info.dim1 ~ty:dom ~cap:vcap' ~sys:vsys'

  | _ -> failwith "car"

and cdr rel v =
  match out v with
  | Cons (_, clo) ->
    eval_clo clo

  | Up (vty, vneu) ->
    let dom, cod = out_sg vty in
    let vcar = car rel v in
    let vcod = inst_bclo cod vcar in
    reflect rel vcod @@ into @@ Cdr vneu

  | Coe info ->
    let vcar = car rel info.tm in
    let vcdr = cdr rel info.tm in
    let dom = bclo_frame KSgDom info.ty in
    let frm = KSgCodCoe {tag = info.tag; dim0 = info.dim0; dom = dom; arg = vcar} in
    let cod = bclo_frame frm info.ty in
    coe ~rel ~tag:info.tag ~dim0:info.dim0 ~dim1:info.dim1 ~ty:cod ~tm:vcdr

  | HCom info ->
    let frm = KSgCodHCom {tag = info.tag; dim0 = info.dim0; dom = clo_frame KSgDom info.ty; cap = info.cap; sys = info.sys} in
    let cod' = {info.ty with foc = Tm.B info.ty.foc; thin = Thin.skip info.ty.thin; stk = frm :: info.ty.stk} in
    let vcap' = cdr rel info.cap in
    let vsys' = map_tubes (bclo_frame KCdr) info.sys in
    com ~rel ~tag:info.tag ~dim0:info.dim0 ~dim1:info.dim1 ~ty:cod' ~cap:vcap' ~sys:vsys'

  | _ -> failwith "cdr"

and reflect rel vty vneu =
  into @@ Up (vty, vneu)

and generic rel vty i =
  reflect rel vty @@ into @@ Lvl i

and reflect_ext rel dom sys vneu =
  match sys with
  | [] -> reflect rel dom vneu
  | (vd0, vd1, clo) :: sys ->
    match DimRel.compare_dim rel vd0 vd1 with
    | DimVal.Same ->
      begin
        match clo with
        | Some clo -> eval_clo clo
        | None -> failwith "reflect_ext: did not expect None in tube"
      end
    | _ -> reflect_ext rel dom sys vneu

and eval_stk stk (rho : env) v =
  match stk with
  | [] -> v
  | frm::stk ->
    eval_frm rho frm @@
    eval_stk stk rho v

and eval_frm rho frm v =
  match frm with
  | KCar ->
    car (Env.rel rho) v

  | KCdr ->
    cdr (Env.rel rho) v

  | KApply varg ->
    apply (Env.rel rho) v varg

  | KComTubeCoe {tag; dim1; ty; tube} ->
    let varg = List.hd rho.vals in
    let tm = inst_bclo tube varg in
    coe ~rel:(Env.rel rho) ~tag ~dim0:varg ~dim1 ~ty ~tm

  | KPiDom ->
    let dom, _ = out_pi v in
    eval_clo dom

  | KPiCodCoe {tag; dim1; dom; arg} ->
    let dimx = List.hd rho.vals in
    let _, cod = out_pi v in
    inst_bclo cod @@
    coe ~rel:(Env.rel rho) ~tag ~dim0:dim1 ~dim1:dimx ~ty:dom ~tm:arg

  | KSgDom ->
    let dom, _ = out_sg v in
    eval_clo dom

  | KSgCodCoe {tag; dim0; dom; arg} ->
    let dimx = List.hd rho.vals in
    let _, cod = out_sg v in
    inst_bclo cod @@
    coe ~rel:(Env.rel rho) ~tag ~dim0 ~dim1:dimx ~ty:dom ~tm:arg

  | KSgCodHCom {tag; dim0; dom; cap; sys} ->
    let dimx = List.hd rho.vals in
    let _, cod = out_sg v in
    let cap' = car (Env.rel rho) cap in
    let sys' = map_tubes (bclo_frame KCar) sys in
    inst_bclo cod @@
    hcom ~rel:(Env.rel rho) ~tag ~dim0 ~dim1:dimx ~ty:dom ~cap:cap' ~sys:sys'

and inst_bclo : bclo -> can t -> can t =
  fun node varg ->
    let Tm.B tm = node.foc in
    eval_stk node.stk (Env.ext node.env varg) @@
    eval (Env.thin node.thin (Env.ext node.env varg)) tm

and eval_clo : tclo -> can t =
  fun node ->
    eval_stk node.stk node.env @@
    eval (Env.thin node.thin node.env) node.foc


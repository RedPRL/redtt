type can = [`Can]
type neu = [`Neu]

type 'a tube = DimVal.t * DimVal.t * 'a option
type 'a system = 'a tube list


type _ f =
  | Lvl : int -> neu f

  | Up : can t * neu t -> can f

  | Pi : tclo * bclo -> can f
  | Sg : tclo * bclo -> can f
  | Ext : can t * tclo system -> can f
  | Univ : Lvl.t -> can f
  | Interval : can f

  | Dim0 : can f
  | Dim1 : can f

  | Lam : bclo -> can f
  | Cons : tclo * tclo -> can f

  | Coe : { dim0 : can t; dim1 : can t; ty : bclo; tm : can t } -> can f
  | HCom : { dim0 : can t; dim1 : can t; ty : tclo; cap : can t; sys : bclo system } -> can f

  | App : neu t * can t -> neu f
  | Car : neu t -> neu f
  | Cdr : neu t -> neu f

and 'a t = { con : 'a f }
and env = can t list

and 'a clo = { foc : 'a; thin : Thin.t; env : env; stk : stk }
and tclo = Tm.chk Tm.t clo
and bclo = Tm.chk Tm.t Tm.bnd clo

and frm =
  | KApply of can t
  | KExtCar of tclo system
  | KCar
  | KCdr
  | KExtApp of tclo system
  | KExtCdr of tclo system
  | KComTubeCoe of {dim1 : can t; ty : bclo; tube : bclo}
  | KPiDom
  | KPiCodCoe of {dim1 : can t; dom : bclo; arg : can t}
  | KSgDom
  | KSgCodCoe of {dim0 : can t; dom : bclo; arg : can t}
  | KSgCodHCom of {dim0 : can t; dom : tclo; cap : can t; sys : bclo system}

and stk = frm list

let into vf =
  {con = vf}


let embed_dimval dv =
  into @@
  match dv with
  | DimVal.Dim0 -> Dim0
  | DimVal.Dim1 -> Dim1
  | DimVal.Lvl i -> Up (into Interval, into @@ Lvl i)

let out : type a. a t -> a f =
  fun node -> node.con


let project_dimval (type a) (v : a t) =
  match out v with
  | Dim0 -> DimVal.Dim0
  | Dim1 -> DimVal.Dim1
  | Up (_, vneu) ->
    begin
      match out vneu with
      | Lvl i -> DimVal.Lvl i
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


let coe ~dim0 ~dim1 ~ty ~tm =
  into @@ Coe {dim0; dim1; ty; tm}

let hcom ~dim0 ~dim1 ~ty ~cap ~sys = 
  into @@ HCom {dim0; dim1; ty; cap; sys}

let com ~dim0 ~dim1 ~ty ~cap ~sys =
  let vcap' = coe ~dim0 ~dim1 ~ty ~tm:cap in
  let Tm.B tm = ty.foc in
  let ty1 = {ty with foc = tm; env = dim1 :: ty.env} in
  let tube bclo' = bclo_frame (KComTubeCoe {dim1 = dim1; ty = ty; tube = bclo'}) ty in
  let vsys' = map_tubes tube sys in
  hcom ~dim0 ~dim1 ~ty:ty1 ~cap:vcap' ~sys:vsys'


let rec out_pi v =
  match out v with
  | Pi (dom, cod) -> dom, cod
  | Ext (vty, vsys) ->
    let dom, cod = out_pi vty in
    dom, bclo_frame (KExtApp vsys) cod
  | _ -> failwith "out_pi"

let rec out_sg v =
  match out v with
  | Sg (dom, cod) -> dom, cod
  | Ext (vty, vsys) ->
    let dom, cod = out_sg vty in
    clo_frame (KExtCar vsys) dom,
    bclo_frame (KExtCdr vsys) cod
  | _ -> failwith "out_sg"


let rec eval : type a. env -> a Tm.t -> can t =
  fun rho tm ->
    match Tm.out tm with
    | Tm.Var i ->
      Thin.proj i rho

    | Tm.Pi (dom, cod) ->
      into @@ Pi (dom <: rho, cod <: rho)

    | Tm.Sg (dom, cod) ->
      into @@ Sg (dom <: rho, cod <: rho)

    | Tm.Ext (ty, sys) ->
      into @@ Ext (eval rho ty, eval_sys rho sys)

    | Tm.Lam bdy ->
      into @@ Lam (bdy <: rho)

    | Tm.Cons (t0, t1) ->
      into @@ Cons (t0 <: rho, t1 <: rho)

    | Tm.Coe info ->
      let vd0 = eval rho info.dim0 in
      let vd1 = eval rho info.dim1 in
      let vtm = eval rho info.tm in
      coe ~dim0:vd0 ~dim1:vd1 ~ty:(info.ty <: rho) ~tm:vtm

    | Tm.HCom info ->
      let vd0 = eval rho info.dim0 in
      let vd1 = eval rho info.dim1 in
      let vcap = eval rho info.cap in
      let vsys = eval_bsys rho info.sys in
      hcom ~dim0:vd0 ~dim1:vd1 ~ty:(info.ty <: rho) ~cap:vcap ~sys:vsys

    | Tm.Com info ->
      let vd0 = eval rho info.dim0 in
      let vd1 = eval rho info.dim1 in
      let vcap = eval rho info.cap in
      let vsys = eval_bsys rho info.sys in
      com ~dim0:vd0 ~dim1:vd1 ~ty:(info.ty <: rho) ~cap:vcap ~sys:vsys

    | Tm.Univ lvl ->
      into @@ Univ lvl

    | Tm.Interval ->
      into Interval

    | Tm.Dim0 ->
      into Dim0

    | Tm.Dim1 ->
      into Dim1

    | Tm.Car t ->
      car @@ eval rho t

    | Tm.Cdr t ->
      cdr @@ eval rho t

    | Tm.App (t1, t2) ->
      apply (eval rho t1) (eval rho t2)

    | Tm.Down t ->
      eval rho t.tm

    | Tm.Up t ->
      eval rho t

and eval_sys rho sys =
  List.map (eval_tube rho) sys

and eval_bsys rho bsys =
  List.map (eval_btube rho) bsys

and eval_tube rho (t0, t1, otm) =
  let vd0 = project_dimval @@ eval rho t0 in
  let vd1 = project_dimval @@ eval rho t1 in
  let ov =
    match vd0, vd1, otm with
    | DimVal.Dim0, DimVal.Dim1, _ -> None
    | DimVal.Dim1, DimVal.Dim0, _ -> None
    | _, _, Some tm -> Some (tm <: rho)
    | _ -> failwith "eval_tube: expected Some"
  in
  (vd0, vd1, ov)

and eval_btube rho (t0, t1, obnd) =
  let vd0 = project_dimval @@ eval rho t0 in
  let vd1 = project_dimval @@ eval rho t1 in
  let ovbnd =
    match vd0, vd1, obnd with
    | DimVal.Dim0, DimVal.Dim1, _ -> None
    | DimVal.Dim1, DimVal.Dim0, _ -> None
    | _, _, Some bnd -> Some (bnd <: rho)
    | _ -> failwith "eval_tube: expected Some"
  in
  (vd0, vd1, ovbnd)


and apply vfun varg =
  match out vfun with
  | Lam bclo ->
    inst_bclo bclo varg

  | Up (vty, vneu) ->
    let dom, cod = out_pi vty in
    let vcod = inst_bclo cod varg in
    reflect vcod @@ into @@ App (vneu, varg)

  | Coe info ->
    let dom = bclo_frame KPiDom info.ty in
    let cod = bclo_frame (KPiCodCoe {dim1 = info.dim1; dom = dom; arg = varg}) info.ty in
    let varg' = coe ~dim0:info.dim1 ~dim1:info.dim0 ~ty:dom ~tm:varg in
    coe ~dim0:info.dim0 ~dim1:info.dim1 ~ty:cod ~tm:(apply info.tm varg')

  | HCom info ->
    let dom, cod = out_pi @@ eval_clo info.ty in
    let Tm.B tm = cod.foc in
    let cod' = {cod with foc = tm; env = varg :: cod.env} in
    let vcap' = apply info.cap varg in
    let vsys' = map_tubes (bclo_frame (KApply varg)) info.sys in
    hcom ~dim0:info.dim0 ~dim1:info.dim1 ~ty:cod' ~cap:vcap' ~sys:vsys'

  | _ -> failwith "apply"

and car v =
  match out v with
  | Cons (clo, _) ->
    eval_clo clo

  | Up (vty, vneu) ->
    let dom, _ = out_sg vty in
    let vdom = eval_clo dom in
    reflect vdom @@ into @@ Car vneu

  | Coe info ->
    let dom = bclo_frame KSgDom info.ty in
    let vcar = car v in
    coe ~dim0:info.dim0 ~dim1:info.dim1 ~ty:dom ~tm:vcar

  | HCom info ->
    let dom, _ = out_sg @@ eval_clo info.ty in
    let vcap' = car info.cap in
    let vsys' = map_tubes (bclo_frame KCar) info.sys in
    hcom ~dim0:info.dim0 ~dim1:info.dim1 ~ty:dom ~cap:vcap' ~sys:vsys'

  | _ -> failwith "car"

and cdr v =
  match out v with
  | Cons (_, clo) ->
    eval_clo clo

  | Up (vty, vneu) ->
    let dom, cod = out_sg vty in
    let vcar = car v in
    let vcod = inst_bclo cod vcar in
    reflect vcod @@ into @@ Cdr vneu

  | Coe info ->
    let vcar = car info.tm in
    let vcdr = cdr info.tm in
    let dom = bclo_frame KSgDom info.ty in
    let frm = KSgCodCoe {dim0 = info.dim0; dom = dom; arg = vcar} in
    let cod = bclo_frame frm info.ty in
    coe ~dim0:info.dim0 ~dim1:info.dim1 ~ty:cod ~tm:vcdr

  | HCom info ->
    let frm = KSgCodHCom {dim0 = info.dim0; dom = clo_frame KSgDom info.ty; cap = info.cap; sys = info.sys} in
    let cod' = {info.ty with foc = Tm.B info.ty.foc; thin = Thin.skip info.ty.thin; stk = frm :: info.ty.stk} in
    let vcap' = cdr info.cap in
    let vsys' = map_tubes (bclo_frame KCdr) info.sys in
    com ~dim0:info.dim0 ~dim1:info.dim1 ~ty:cod' ~cap:vcap' ~sys:vsys'

  | _ -> failwith "cdr"

and reflect vty vneu =
  match out vty with
  | Ext (dom, sys) ->
    reflect_ext dom sys vneu
  | _ -> into @@ Up (vty, vneu)

and reflect_ext dom sys vneu =
  match sys with
  | [] -> reflect dom vneu
  | (vd0, vd1, clo) :: sys ->
    if dim_eq vd0 vd1 then
      match clo with
      | Some clo -> eval_clo clo
      | None -> failwith "reflect_ext: did not expect None in tube"
    else
      reflect_ext dom sys vneu

and dim_eq vd0 vd1 =
  match vd0, vd1 with
  | DimVal.Dim0, DimVal.Dim0 -> true
  | DimVal.Dim1, DimVal.Dim1 -> true
  | DimVal.Lvl i, DimVal.Lvl j -> i = j
  | _ -> false


and eval_stk stk rho v =
  match stk with
  | [] -> v
  | frm::stk ->
    eval_frm rho frm @@
    eval_stk stk rho v

and eval_frm rho frm v =
  match frm with
  | KCar ->
    car v

  | KCdr ->
    cdr v

  | KApply varg ->
    apply v varg

  | KExtCar sys ->
    into @@ Ext (v, map_tubes (clo_frame KCar) sys)

  | KExtCdr sys ->
    into @@ Ext (v, map_tubes (clo_frame KCdr) sys)

  | KExtApp sys ->
    let varg = List.hd rho in
    into @@ Ext (v, map_tubes (clo_frame (KApply varg)) sys)

  | KComTubeCoe {dim1; ty; tube} ->
    let varg = List.hd rho in
    let tm = inst_bclo tube varg in
    coe ~dim0:varg ~dim1 ~ty ~tm

  | KPiDom ->
    let dom, _ = out_pi v in
    eval_clo dom

  | KPiCodCoe {dim1; dom; arg} ->
    let dimx = List.hd rho in
    let _, cod = out_pi v in
    inst_bclo cod @@
    coe ~dim0:dim1 ~dim1:dimx ~ty:dom ~tm:arg

  | KSgDom ->
    let dom, _ = out_sg v in
    eval_clo dom

  | KSgCodCoe {dim0; dom; arg} ->
    let dimx = List.hd rho in
    let _, cod = out_sg v in
    inst_bclo cod @@
    coe ~dim0 ~dim1:dimx ~ty:dom ~tm:arg

  | KSgCodHCom {dim0; dom; cap; sys} ->
    let dimx = List.hd rho in
    let _, cod = out_sg v in
    inst_bclo cod @@
    hcom ~dim0 ~dim1:dimx ~ty:dom ~cap:(car cap) ~sys:(map_tubes (bclo_frame KCar) sys)

and inst_bclo : bclo -> can t -> can t =
  fun node varg ->
    let Tm.B tm = node.foc in
    eval_stk node.stk (varg :: node.env) @@
    eval (Thin.act node.thin @@ varg :: node.env) tm

and eval_clo : tclo -> can t =
  fun node ->
    eval_stk node.stk node.env @@
    eval (Thin.act node.thin @@ node.env) node.foc


type can = [`Can]
type neu = [`Neu]

type 'a bnd = B of 'a

(* TODO: reformulate using closures with suspended stacks instead of DimFam;
   I believe that this should scale up to even things as complicated as
   coe in V-types, etc. *)

type _ f =
  | Lvl : int -> neu f

  | Up : can t * neu t -> can f

  | Pi : clo * bclo -> can f
  | Sg : clo * bclo -> can f
  | Ext : can t * clo system -> can f
  | Univ : Lvl.t -> can f
  | Interval : can f

  | Dim0 : can f
  | Dim1 : can f

  | Lam : bclo -> can f
  | Cons : clo * clo -> can f

  | Coe : can t * can t * bclo * can t -> can f

  | HCom : can t * can t * clo * can t * bclo system -> can f

  | App : neu t * can t -> neu f
  | Car : neu t -> neu f
  | Cdr : neu t -> neu f

and 'a t = { con : 'a f }

and 'a tube = DimVal.t * DimVal.t * 'a option
and 'a system = 'a tube list

and env = can t list
and clo = Clo of Tm.chk Tm.t * env * stk
and bclo = BClo of Tm.chk Tm.t Tm.bnd * env * stk

and frm =
  | KApply of can t
  | KExtCar of clo system
  | KCar
  | KCdr
  | KExtApp of clo system
  | KExtCdr of clo system
  | KComTubeCoe of {dim1 : can t; ty : bclo; tube : bclo}
  | KPiDom
  | KPiCodCoe of {dim1 : can t; dom : bclo; arg : can t}
  | KSgDom
  | KSgCodCoe of {dim0 : can t; dom : bclo; arg : can t}
  | KSgCodHCom of {dim0 : can t; dom : clo; cap : can t; sys : bclo system}

and stk = frm list

let into vf =
  {con = vf}


let embed_dimval dv =
  match dv with
  | DimVal.Dim0 -> into Dim0
  | DimVal.Dim1 -> into Dim1
  | DimVal.Lvl i -> into @@ Up (into Interval, into @@ Lvl i)

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

let (<:) tm rho : clo =
  Clo (tm, rho, [])

let (<:+) bnd rho =
  BClo (bnd, rho, [])


let map_tubes f =
  List.map @@ fun (vd0, vd1, vbnd) ->
  (vd0, vd1, Option.map f vbnd)


let rec eval : type a. env -> a Tm.t -> can t =
  fun rho tm ->
    match Tm.out tm with
    | Tm.Var i ->
      let v = Thin.proj i rho in
      v

    | Tm.Pi (dom, cod) ->
      into @@ Pi (dom <: rho, cod <:+ rho)

    | Tm.Sg (dom, cod) ->
      into @@ Sg (dom <: rho, cod <:+ rho)

    | Tm.Ext (ty, sys) ->
      into @@ Ext (eval rho ty, eval_sys rho sys)

    | Tm.Lam bdy ->
      into @@ Lam (bdy <:+ rho)

    | Tm.Cons (t0, t1) ->
      into @@ Cons (t0 <: rho, t1 <: rho)

    | Tm.Coe (d0, d1, bnd, tm) ->
      let vd0 = eval rho d0 in
      let vd1 = eval rho d1 in
      let vtm = eval rho tm in
      into @@ Coe (vd0, vd1, bnd <:+ rho, vtm)

    | Tm.HCom (d0, d1, ty, cap, sys) ->
      let vd0 = eval rho d0 in
      let vd1 = eval rho d1 in
      let vcap = eval rho cap in
      let vsys = eval_bsys rho sys in
      into @@ HCom (vd0, vd1, ty <: rho, vcap, vsys)

    | Tm.Com (d0, d1, bnd, cap, sys) ->
      let vd0 = eval rho d0 in
      let vd1 = eval rho d1 in
      let vcap = eval rho cap in
      let vsys = eval_bsys rho sys in
      com (vd0, vd1, bnd <:+ rho, vcap, vsys)

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

and out_pi v =
  match out v with
  | Pi (dom, cod) -> dom, cod
  | Ext (vty, vsys) ->
    let dom, cod = out_pi vty in
    dom, bclo_frame (KExtApp vsys) cod
  | _ -> failwith "out_pi"

and out_sg v =
  match out v with
  | Sg (dom, cod) -> dom, cod
  | Ext (vty, vsys) ->
    let dom, cod = out_sg vty in
    clo_frame (KExtCar vsys) dom,
    bclo_frame (KExtCdr vsys) cod
  | _ -> failwith "out_sg"

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
    | _, _, Some bnd -> Some (bnd <:+ rho)
    | _ -> failwith "eval_tube: expected Some"
  in
  (vd0, vd1, ovbnd)


and com (vd0, vd1, bclo, vcap, vsys) =
  let vcap' = into @@ Coe (vd0, vd1, bclo, vcap) in
  let BClo (Tm.B tm, rho, stk) = bclo in
  let ty = Clo (tm, vd1 :: rho, stk) in
  let tube bclo' = bclo_frame (KComTubeCoe {dim1 = vd1; ty = bclo; tube = bclo'}) bclo in
  let vsys' = map_tubes tube vsys in
  into @@ HCom (vd0, vd1, ty, vcap', vsys')

and apply vfun varg =
  match out vfun with
  | Lam bclo ->
    inst_bclo bclo varg

  | Up (vty, vneu) ->
    let dom, cod = out_pi vty in
    let vcod = inst_bclo cod varg in
    reflect vcod @@ into @@ App (vneu, varg)

  | Coe (vd0, vd1, vbnd, vfun) ->
    let dom = bclo_frame KPiDom vbnd in
    let cod = bclo_frame (KPiCodCoe {dim1 = vd1; dom = dom; arg = varg}) vbnd in
    let varg' = into @@ Coe (vd1, vd0, dom, varg) in
    into @@ Coe (vd0, vd1, cod, apply vfun varg')

  | HCom (vd0, vd1, vty, vcap, vsys) ->
    let dom, cod = out_pi @@ eval_clo vty in
    let BClo (Tm.B tm, rho, stk) = cod in
    let cod' = Clo (tm, varg :: rho, stk) in
    let vcap' = apply vcap varg in
    let vsys' = map_tubes (bclo_frame (KApply varg)) vsys in
    into @@ HCom (vd0, vd1, cod', vcap', vsys')

  | _ -> failwith "apply"

and car v =
  match out v with
  | Cons (clo, _) ->
    eval_clo clo

  | Up (vty, vneu) ->
    let dom, _ = out_sg vty in
    let vdom = eval_clo dom in
    reflect vdom @@ into @@ Car vneu

  | Coe (vd0, vd1, bclo, v) ->
    let dom = bclo_frame KSgDom bclo in
    let vcar = car v in
    into @@ Coe (vd0, vd1, dom, vcar)

  | HCom (vd0, vd1, vty, vcap, vsys) ->
    let dom, _ = out_sg @@ eval_clo vty in
    let vcap' = car vcap in
    let vsys' = map_tubes (bclo_frame KCar) vsys in
    into @@ HCom (vd0, vd1, dom, vcap', vsys')

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

  | Coe (vd0, vd1, bclo, v) ->
    let vcar = car v in
    let vcdr = cdr v in
    let dom = bclo_frame KSgDom bclo in
    let frm = KSgCodCoe {dim0 = vd0; dom = dom; arg = vcar} in
    let cod = bclo_frame frm bclo in
    into @@ (Coe (vd0, vd1, cod, vcdr))

  | HCom (vd0, vd1, ty, vcap, vsys) ->
    let Clo (tty, rho, stk) = ty in
    let bty = Tm.B (Tm.thin (Thin.skip Thin.id) tty) in
    let frm = KSgCodHCom {dim0 = vd0; dom = clo_frame KSgDom ty; cap = vcap; sys = vsys} in
    let cod' = BClo (bty, rho, frm :: stk) in
    let vcap' = cdr vcap in
    let vsys' = map_tubes (bclo_frame KCdr) vsys in
    com (vd0, vd1, cod', vcap', vsys')

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

and inst_bclo : bclo -> can t -> can t =
  fun (BClo (Tm.B tm, rho, stk)) varg ->
    let rho' = varg :: rho in
    let v = eval rho' tm in
    eval_stk stk rho' v


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
    into @@ Coe (varg, dim1, ty, inst_bclo tube varg)
  | KPiDom ->
    let dom, _ = out_pi v in
    eval_clo dom
  | KPiCodCoe {dim1; dom; arg} ->
    let dimx = List.hd rho in
    let _, cod = out_pi v in
    let coe = into @@ Coe (dim1, dimx, dom, arg) in
    inst_bclo cod coe
  | KSgDom ->
    let dom, _ = out_sg v in
    eval_clo dom
  | KSgCodCoe {dim0; dom; arg} ->
    let dimx = List.hd rho in
    let _, cod = out_sg v in
    let coe = into @@ Coe (dim0, dimx, dom, arg) in
    inst_bclo cod coe
  | KSgCodHCom {dim0; dom; cap; sys} ->
    let dimx = List.hd rho in
    let _, cod = out_sg v in
    let hcom = into @@ HCom (dim0, dimx, dom, car cap, map_tubes (bclo_frame KCar) sys) in
    inst_bclo cod hcom


and eval_clo : clo -> can t =
  fun (Clo (tm, rho, stk)) ->
    eval_stk stk rho (eval rho tm)


and clo_frame : frm -> clo -> clo =
  fun frm clo ->
    let Clo (tm, rho, stk) = clo in
    Clo (tm, rho, frm :: stk)

and bclo_frame : frm -> bclo -> bclo =
  fun frm bclo ->
    let BClo (tm, rho, bstk) = bclo in
    BClo (tm, rho, frm :: bstk)
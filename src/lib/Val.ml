type can = [`Can]
type neu = [`Neu]

type 'a bnd = B of 'a

type 'a dimfam = 'a DimFam.t

type _ f = 
  | Lvl : int -> neu f

  | Up : can t * neu t -> can f

  | Pi : clo * bclo -> can f
  | Sg : clo * bclo -> can f
  | Ext : clo * clo system -> can f
  | Univ : Lvl.t -> can f
  | Interval : can f

  | Dim0 : can f
  | Dim1 : can f

  | Lam : bclo -> can f
  | Cons : clo * clo -> can f

  | Coe : can t * can t * can t dimfam * can t -> can f

  | HCom : can t * can t * can t * can t * can t dimfam system -> can f

  | App : neu t * can t -> neu f
  | Car : neu t -> neu f
  | Cdr : neu t -> neu f

and 'a t = { con : 'a f }

and 'a tube = DimVal.t * DimVal.t * 'a option
and 'a system = 'a tube list

and env = can t list
and clo = [`Eval of Tm.chk Tm.t * env | `Ret of can t] ref
and bclo = BClo of Tm.chk Tm.t Tm.bnd * env

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

let (<:) tm rho =
  ref @@ `Eval (tm, rho)

let (<:+) bnd rho = 
  BClo (bnd, rho)


let map_tubes f = 
  List.map @@ fun (vd0, vd1, vbnd) ->
  (vd0, vd1, Option.map f vbnd)


let map_btubes f = 
  map_tubes (DimFam.map f)


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
      let v = Thin.proj i rho in
      v

    | Tm.Pi (dom, cod) ->
      into @@ Pi (dom <: rho, cod <:+ rho)

    | Tm.Sg (dom, cod) ->
      into @@ Sg (dom <: rho, cod <:+ rho)

    | Tm.Ext (ty, sys) ->
      into @@ Ext (ty <: rho, eval_sys rho sys)

    | Tm.Lam bdy ->
      into @@ Lam (bdy <:+ rho)

    | Tm.Cons (t0, t1) ->
      into @@ Cons (t0 <: rho, t1 <: rho)

    | Tm.Coe (d0, d1, Tm.B ty, tm) ->
      let vd0 = eval rho d0 in
      let vd1 = eval rho d1 in
      let vty = DimFam.make (fun x -> eval (embed_dimval x :: rho) ty) in
      let vtm = eval rho tm in
      into @@ Coe (vd0, vd1, vty, vtm)

    | Tm.HCom (d0, d1, ty, cap, sys) ->
      let vd0 = eval rho d0 in
      let vd1 = eval rho d1 in
      let vty = eval rho ty in 
      let vcap = eval rho cap in
      let vsys = eval_bsys rho sys in
      into @@ HCom (vd0, vd1, vty, vcap, vsys)

    | Tm.Com (d0, d1, Tm.B ty, cap, sys) ->
      let vd0 = eval rho d0 in
      let vd1 = eval rho d1 in
      let vty = DimFam.make (fun x -> eval (embed_dimval x :: rho) ty) in
      let vcap = eval rho cap in
      let vsys = eval_bsys rho sys in
      com (vd0, vd1, vty, vcap, vsys)

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
    | _, _, Some (Tm.B tm) ->
      let vbnd = 
        DimFam.make @@ fun x ->
        eval (embed_dimval x :: rho) tm
      in
      Some vbnd
    | _ -> failwith "eval_tube: expected Some"
  in
  (vd0, vd1, ovbnd)



and com (vd0, vd1, vbnd, vcap, vsys) =
  let vcap' = into @@ Coe (vd0, vd1, vbnd, vcap) in
  let vty' = DimFam.inst vbnd @@ project_dimval vd1 in
  let tube vbnd = 
    DimFam.make @@ fun x ->
    into @@ Coe (embed_dimval x, vd1, vbnd, DimFam.inst vbnd x)
  in
  let vsys' = map_tubes tube vsys in
  into @@ HCom (vd0, vd1, vty', vcap', vsys')

and out_bind_pi vbnd = 
  DimFam.split @@ DimFam.map out_pi vbnd

and out_bind_sg vbnd = 
  DimFam.split @@ DimFam.map out_sg vbnd

and apply vfun varg = 
  match out vfun with 
  | Lam bclo ->
    inst_bclo bclo varg

  | Up (vty, vneu) ->
    let dom, cod = out_pi vty in
    let vcod = inst_bclo cod varg in
    reflect vcod @@ into @@ App (vneu, varg)

  | Coe (vd0, vd1, vbnd, vfun) ->
    let dom, cod = out_bind_pi vbnd in
    let vdom = DimFam.map eval_clo dom in
    let vcod =
      DimFam.make @@ fun x -> 
      let coe = into @@ Coe (vd1, embed_dimval x, vdom, varg) in
      inst_bclo (DimFam.inst cod x) coe
    in
    let coe = into @@ Coe (vd1, vd0, vdom, varg) in
    into @@ Coe (vd0, vd1, vcod, apply vfun coe)

  | HCom (vd0, vd1, vty, vcap, vsys) ->
    let dom, cod = out_pi vty in
    let vcod = inst_bclo cod varg in
    let vcap' = apply vcap varg in
    let vsys' = map_btubes (fun v -> apply v varg) vsys in
    into @@ HCom (vd0, vd1, vcod, vcap', vsys')

  | _ -> failwith "apply"

and car v = 
  match out v with 
  | Cons (clo, _) ->
    eval_clo clo

  | Up (vty, vneu) -> 
    let dom, cod = out_sg vty in
    let vdom = eval_clo dom in
    reflect vdom @@ into @@ Car vneu

  | Coe (vd0, vd1, vbnd, v) ->
    let dom, cod = out_bind_sg vbnd in
    let vdom = DimFam.map eval_clo dom in
    let vcar = car v in
    into @@ Coe (vd0, vd1, vdom, vcar)


  | HCom (vd0, vd1, vty, vcap, vsys) ->
    let dom, cod = out_sg vty in
    let vdom = eval_clo dom in
    let vcap' = car vcap in
    let vsys' = map_btubes car vsys in
    into @@ HCom (vd0, vd1, vdom, vcap', vsys')

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

  | Coe (vd0, vd1, vbnd, v) -> 
    let dom, cod = out_bind_pi vbnd in
    let vdom = DimFam.map eval_clo dom in
    let vcar = car v in
    let vcod =
      DimFam.make @@ fun x -> 
      let coe = into @@ Coe (vd0, embed_dimval x, vdom, vcar) in
      inst_bclo (DimFam.inst cod x) coe
    in
    into @@ Coe (vd0, vd1, vcod, cdr v)

  | HCom (vd0, vd1, vty, vcap, vsys) ->
    let dom, cod = out_sg vty in
    let vdom = eval_clo dom in
    let vcod = 
      DimFam.make @@ fun x ->
      let hcom = into @@ HCom (vd0, embed_dimval x, vdom, car vcap, map_btubes car vsys) in
      inst_bclo cod hcom in
    let vcap' = cdr vcap in
    let vsys' = map_btubes cdr vsys in
    com (vd0, vd1, vcod, vcap', vsys')

  | _ -> failwith "cdr"

and reflect vty vneu =
  match out vty with
  | Ext (dom, sys) ->
    reflect_ext dom sys vneu
  | _ -> into @@ Up (vty, vneu)

and reflect_ext dom sys vneu = 
  match sys with 
  | [] -> reflect (eval_clo dom) vneu
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
  fun (BClo (Tm.B tm, vrho)) v ->
    eval (v :: vrho) tm

and eval_clo : clo -> can t = 
  fun clo ->
    match !clo with 
    | `Eval (tm, rho) ->
      let v = eval rho tm in
      clo := `Ret v;
      v
    | `Ret v -> v
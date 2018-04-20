type can = [`Can]
type neu = [`Neu]

type rel = DimRel.t

type 'a env_ = { vals : 'a list; rel : DimRel.t }

module Tube = 
struct
  type equ = DimVal.equ

  type 'a t = 
    | Indeterminate of equ * 'a
    | True of 'a
    | False of equ
    | Delete

  let get_equ tb = 
    match tb with
    | Indeterminate (equ, _) -> Some equ
    | True a -> None
    | False equ -> Some equ
    | Delete -> None

  let proj tb = 
    match tb with
    | Indeterminate (_, a) -> a
    | True a -> a
    | Delete -> failwith "Tube.proj: filtered equation"
    | False _ -> failwith "Tube.proj: false equation"

end

type 'a tube = 'a Tube.t
type 'a system = 'a tube list

module Clo = 
struct
  type 'a tclo = 
    | Eval of {env : 'a env_; tm : Tm.chk Tm.t}
    | Inst of 'a bclo * 'a

  and 'a bclo =
    (* wait for an argument, and then extend the environment and eval *)
    | Await of {env : 'a env_; btm : Tm.chk Tm.t Tm.bnd}
    | SgDom of 'a bclo
    | PiDom of 'a bclo
    | PiCodCoe of {bclo : 'a bclo; dim1 : DimVal.t; dom : 'a bclo; arg : 'a}
    | ExtCod of 'a bclo * DimVal.t
    | ExtSysTube of 'a bclo * int * DimVal.t
    | App of 'a bclo * 'a
    | Car of 'a bclo
    | Wk of 'a tclo

  type 'a sclo = 
    | SysAwait of {env : 'a env_; sys : Tm.chk Tm.t system}
end

type _ f =
  | Lvl : int -> neu f

  | Up : can t * neu t -> can f

  | Pi : tclo * bclo -> can f
  | Sg : tclo * bclo -> can f
  | Ext : bclo * sclo -> can f

  | Univ : Lvl.t -> can f
  | Interval : can f

  | Dim0 : can f
  | Dim1 : can f
  | DimGen : can f

  | Lam : bclo -> can f
  | Cons : tclo * tclo -> can f

  | Coe : {dim0 : DimVal.t; dim1 : DimVal.t; ty : bclo; tm : can t} -> can f
  | HCom : {dim0 : DimVal.t; dim1 : DimVal.t; ty : can t; cap : can t; sys : bclo system} -> can f

  | FunApp : neu t * can t -> neu f
  | ExtApp : neu t * DimVal.t -> neu f

  | Car : neu t -> neu f
  | Cdr : neu t -> neu f

and 'a t = { con : 'a f }
and env = can t env_
and tclo = can t Clo.tclo
and bclo = can t Clo.bclo
and sclo = can t Clo.sclo



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
  | DimVal.Lvl i -> Up (into Interval, into @@ Lvl i)
  | DimVal.Gen -> DimGen

let out : type a. a t -> a f =
  fun node -> node.con


let project_dimval (type a) (v : a t) =
  match out v with
  | Dim0 -> DimVal.Dim0
  | Dim1 -> DimVal.Dim1
  | Up (vty, vneu) ->
    begin
      match out vty, out vneu with
      | Interval, Lvl i -> DimVal.Lvl i 
      | _ -> failwith "project_dimval/Up"
    end
  | DimGen -> DimVal.Gen
  | _ -> failwith "project_dimval"

let (<:) tm env = 
  Clo.Eval {tm; env}

let (<:+) btm env =
  Clo.Await {btm; env}

let out_pi v =
  match out v with
  | Pi (dom, cod) -> dom, cod
  | _ -> failwith "out_pi"

let out_sg v =
  match out v with
  | Sg (dom, cod) -> dom, cod
  | _ -> failwith "out_sg"

let out_ext v =
  match out v with
  | Ext (cod, sys) -> cod, sys
  | _ -> failwith "out_ext"

let mapi_tubes f =
  List.mapi @@ fun i tube ->
  match tube with
  | Tube.Indeterminate (equ, a) ->
    Tube.Indeterminate (equ, f i a)
  | Tube.True a ->
    Tube.True (f i a)
  | Tube.False equ ->
    Tube.False equ
  | Tube.Delete ->
    Tube.Delete


let map_tubes f =
  mapi_tubes (fun i -> f)


let com ~dim0 ~dim1 ~ty ~cap ~sys =
  let _cap' = into @@ Coe {dim0; dim1; ty; tm = cap} in
  failwith "TODO: com"
(* let vcap' = coe ~rel ~dim0 ~dim1 ~ty ~tm:cap in
   let Tm.B tm = ty.foc in
   let ty1 = {ty with foc = tm; env = Env.ext ty.env dim1} in
   let tube bclo' = bclo_frame (KComTubeCoe {dim1 = dim1; ty = ty; tube = bclo'}) ty in
   let vsys' = map_tubes tube sys in
   hcom ~rel ~dim0 ~dim1 ~ty:ty1 ~cap:vcap' ~sys:vsys' *)


let rec eval : type a. env -> a Tm.t -> can t =
  fun rho tm ->
    match Tm.out tm with
    | Tm.Var i ->
      Env.lookup i rho

    | Tm.Pi (dom, cod) ->
      into @@ Pi (dom <: rho, cod <:+ rho)

    | Tm.Sg (dom, cod) ->
      into @@ Sg (dom <: rho, cod <:+ rho)

    | Tm.Lam bdy ->
      into @@ Lam (bdy <:+ rho)

    | Tm.Cons (t0, t1) ->
      into @@ Cons (t0 <: rho, t1 <: rho)

(*
    | Tm.Coe info ->
      let vd0 = eval rho info.dim0 in
      let vd1 = eval rho info.dim1 in
      let vtm = eval rho info.tm in
      coe ~rel:(Env.rel rho) ~dim0:vd0 ~dim1:vd1 ~ty:(info.ty <: rho) ~tm:vtm

    | Tm.HCom info ->
      let vd0 = eval rho info.dim0 in
      let vd1 = eval rho info.dim1 in
      let vcap = eval rho info.cap in
      let vsys = eval_bsys rho info.sys in
      hcom ~rel:(Env.rel rho) ~dim0:vd0 ~dim1:vd1 ~ty:(info.ty <: rho) ~cap:vcap ~sys:vsys

    | Tm.Com info ->
      let vd0 = eval rho info.dim0 in
      let vd1 = eval rho info.dim1 in
      let vcap = eval rho info.cap in
      let vsys = eval_bsys rho info.sys in
      com ~rel:(Env.rel rho) ~dim0:vd0 ~dim1:vd1 ~ty:(info.ty <: rho) ~cap:vcap ~sys:vsys

*)

    | Tm.Univ lvl ->
      into @@ Univ lvl

    | Tm.Interval ->
      into @@ Interval

    | Tm.Dim0 ->
      into Dim0

    | Tm.Dim1 ->
      into Dim1

    | Tm.Car t ->
      car @@ eval rho t

    | Tm.Cdr t ->
      failwith ""
    (* cdr (Env.rel rho) @@ eval rho t *)

    | Tm.App (t1, t2) ->
      apply (eval rho t1) (eval rho t2)

    | Tm.Down t ->
      eval rho t.tm

    | Tm.Up t ->
      eval rho t

    | _ -> failwith "TODO"


and apply vfun varg =
  match out vfun with
  | Lam bclo ->
    inst_bclo bclo varg

  | Up (vty, vneu) ->
    let dom, cod = out_pi vty in
    let vcod = inst_bclo cod varg in
    into @@ Up (vcod, into @@ FunApp (vneu, varg))

  | Coe info ->
    let dom = Clo.PiDom info.ty in
    let cod = Clo.PiCodCoe {bclo = info.ty; dim1 = info.dim1; dom = dom; arg = varg} in
    let varg' = into @@ Coe {dim0 = info.dim1; dim1 = info.dim1; ty = dom; tm = varg} in
    into @@ Coe {dim0 = info.dim0; dim1 = info.dim1; ty = cod; tm = apply info.tm varg'}

  | HCom info ->
    let dom, cod = out_pi info.ty in
    let vcod = inst_bclo cod varg in
    let vcap = apply info.cap varg in
    let vsys = map_tubes (fun bclo -> Clo.App (bclo, varg)) info.sys in
    into @@ HCom {dim0 = info.dim1; dim1 = info.dim1; ty = vcod; cap = vcap; sys = vsys}

  | _ -> failwith "apply"

and ext_apply vext vdim =
  match out vext with 
  | Lam bclo ->
    inst_bclo bclo @@ embed_dimval vdim

  | Up (vty, vneu) ->
    let cod, sclo = out_ext vty in
    let sys = inst_sclo sclo vdim in
    begin
      match project_sys sys with
      | Some v ->
        v
      | None ->
        let vcod = inst_bclo cod @@ embed_dimval vdim in
        into @@ Up (vcod, into @@ ExtApp (vneu, vdim))
    end

  | Coe info ->
    let ty = Clo.ExtCod (info.ty, vdim) in
    let cap = ext_apply info.tm vdim in
    let _, sclo = out_ext @@ inst_bclo info.ty @@ into DimGen in
    let sys = inst_sclo sclo vdim in
    let sys' = mapi_tubes (fun i _ -> Clo.ExtSysTube (info.ty, i, vdim)) sys in
    com ~dim0:info.dim0 ~dim1:info.dim1 ~ty ~cap ~sys:sys'

  | HCom info ->
    let cap = ext_apply info.cap vdim in
    let cod, sclo = out_ext info.ty in
    let ty = inst_bclo cod @@ embed_dimval vdim in
    let rsys = inst_sclo sclo vdim in
    begin
      match project_sys rsys with
      | Some v -> v
      | None -> 
        let sys = map_tubes (fun tb -> Clo.Wk tb) rsys in
        into @@ HCom {dim0 = info.dim0; dim1 = info.dim1; ty; cap; sys = sys @ info.sys}
    end

  | _ ->
    failwith "ext_apply"

and car v =
  match out v with
  | Cons (clo, _) ->
    eval_clo clo

  | Up (vty, vneu) ->
    let dom, _ = out_sg vty in
    let vdom = eval_clo dom in
    into @@ Up (vdom, into @@ Car vneu)

  | Coe info ->
    let vcar = car info.tm in
    into @@ Coe {dim0 = info.dim0; dim1 = info.dim1; ty = failwith "TODO"; tm = vcar}
  (* let dom = bclo_frame KSgDom info.ty in
     let vcar = car rel v in
     coe ~rel:rel ~dim0:info.dim0 ~dim1:info.dim1 ~ty:dom ~tm:vcar *)

  | HCom info ->
    failwith ""
  (* let dom, _ = out_sg @@ eval_clo info.ty in
     let vcap' = car rel info.cap in
     let vsys' = map_tubes (bclo_frame KCar) info.sys in
     hcom ~rel ~dim0:info.dim0 ~dim1:info.dim1 ~ty:dom ~cap:vcap' ~sys:vsys' *)

  | _ -> failwith "car"

and project_bsys sys r =
  match sys with 
  | [] ->
    None
  | Tube.True tb :: sys ->
    Some (inst_bclo tb r)
  | _ :: sys ->
    project_bsys sys r


and project_sys sys =
  match sys with 
  | [] ->
    None
  | Tube.True tb :: sys ->
    Some (eval_clo tb)
  | _ :: sys ->
    project_sys sys

and inst_bclo bclo arg =
  match bclo with 
  | Clo.Await {btm; env} ->
    let Tm.B tm = btm in
    eval (Env.ext env arg) tm

  | Clo.SgDom bclo ->
    let dom, _ = out_sg @@ inst_bclo bclo arg in
    eval_clo dom

  | Clo.PiDom bclo -> 
    let dom, _ = out_pi @@ inst_bclo bclo arg in
    eval_clo dom

  | Clo.PiCodCoe {bclo; dim1; dom; arg = arg'} ->
    let dimx = project_dimval arg in
    let _, cod = out_pi @@ inst_bclo bclo arg in
    let coe = into @@ Coe {dim0 = dim1; dim1 = dimx; ty = dom; tm = arg'} in
    inst_bclo cod coe

  | Clo.ExtCod (bclo, vdim) ->
    let cod, _ = out_ext @@ inst_bclo bclo arg in
    inst_bclo cod @@ embed_dimval vdim

  | Clo.ExtSysTube (bclo, i, arg') ->
    let _, sclo = out_ext @@ inst_bclo bclo arg in
    let sys = inst_sclo sclo arg' in
    eval_clo @@ Tube.proj @@ List.nth sys i

  | Clo.App (bclo, arg') ->
    let v = inst_bclo bclo arg in
    apply v arg'

  | Clo.Car bclo ->
    let v = inst_bclo bclo arg in
    car v

  | Clo.Wk tclo -> 
    eval_clo tclo

and inst_sclo sclo arg = 
  match sclo with
  | Clo.SysAwait {sys; env} ->
    failwith "TODO"

and eval_clo clo =
  match clo with
  | Clo.Eval {tm; env} ->
    eval env tm

  | Clo.Inst (bclo, arg) ->
    inst_bclo bclo arg
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
    | PiCodCoe of {bclo : 'a bclo; dim1 : DimVal.t; arg : 'a}
    | SgCodCoe of {bclo : 'a bclo; dim0 : DimVal.t; arg : 'a}
    | SgCodHCom of {ty : 'a; dim0 : DimVal.t; cap : 'a; sys : 'a bclo system}
    | ExtCod of 'a bclo * DimVal.t
    | ExtSysTube of 'a bclo * int * DimVal.t
    | ComCoeTube of {bclo : 'a bclo; ty : 'a bclo; dim1 : DimVal.t}
    | App of 'a bclo * 'a
    | Car of 'a bclo
    | Cdr of 'a bclo
    | Wk of 'a tclo

  type 'a sclo = 
    | SysAwait of {env : 'a env_; sys : Tm.chk Tm.t Tm.system Tm.bnd}
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

let (<<:+) sys env = 
  Clo.SysAwait {sys; env}

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

let rec eval : type a. env -> a Tm.t -> can t =
  fun rho tm ->
    match Tm.out tm with
    | Tm.Var i ->
      Env.lookup i rho

    | Tm.Pi (dom, cod) ->
      into @@ Pi (dom <: rho, cod <:+ rho)

    | Tm.Ext (Tm.B (cod, sys)) ->
      into @@ Ext (Tm.B cod <:+ rho, Tm.B sys <<:+ rho)

    | Tm.Sg (dom, cod) ->
      into @@ Sg (dom <: rho, cod <:+ rho)

    | Tm.Lam bdy ->
      into @@ Lam (bdy <:+ rho)

    | Tm.Cons (t0, t1) ->
      into @@ Cons (t0 <: rho, t1 <: rho)

    | Tm.Coe info ->
      let dim0 = project_dimval @@ eval rho info.dim0 in
      let dim1 = project_dimval @@ eval rho info.dim1 in
      begin
        match Env.compare_dim rho dim0 dim1 with
        | DimVal.Same ->
          eval rho info.tm
        | _ ->
          let ty = info.ty <:+ rho in
          let tm = eval rho info.tm in
          rigid_coe ~dim0 ~dim1 ~ty ~tm
      end

    | Tm.HCom info ->
      let dim0 = project_dimval @@ eval rho info.dim0 in
      let dim1 = project_dimval @@ eval rho info.dim1 in
      begin
        match Env.compare_dim rho dim0 dim1 with
        | DimVal.Same ->
          eval rho info.cap
        | _ ->
          let sys = eval_bsys rho info.sys in
          match project_bsys sys dim1 with
          | Some v -> v
          | None ->
            let ty = eval rho info.ty in
            let cap = eval rho info.cap in
            rigid_hcom ~dim0 ~dim1 ~ty ~cap ~sys
      end

    | Tm.Com info ->
      let dim0 = project_dimval @@ eval rho info.dim0 in 
      let dim1 = project_dimval @@ eval rho info.dim1 in
      let bty = info.ty <:+ rho in
      let cap =
        let tm = eval rho info.cap in
        rigid_coe ~dim0 ~dim1 ~ty:bty ~tm
      in
      begin
        match Env.compare_dim rho dim0 dim1 with
        | DimVal.Same ->
          cap
        | _ ->
          let ty = inst_bclo bty @@ embed_dimval dim1 in
          let sys = map_tubes (fun bclo -> Clo.ComCoeTube {bclo; ty = bty; dim1}) @@ eval_bsys rho info.sys in
          match project_bsys sys dim1 with 
          | Some v -> v
          | None -> rigid_hcom ~dim0 ~dim1 ~ty ~cap ~sys
      end

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

and rigid_com ~dim0 ~dim1 ~ty ~cap ~sys =
  let cap' = rigid_coe ~dim0 ~dim1 ~ty ~tm:cap in
  let ty' = inst_bclo ty @@ embed_dimval dim1 in
  let sys' = map_tubes (fun bclo -> Clo.ComCoeTube {bclo; ty; dim1}) sys in
  rigid_hcom ~dim0 ~dim1 ~ty:ty' ~cap:cap' ~sys:sys'

and rigid_hcom ~dim0 ~dim1 ~ty ~cap ~sys = 
  match out ty with
  (* TODO: for base types, do something *)
  | _ ->
    into @@ HCom {dim0; dim1; ty; cap; sys}

and rigid_coe ~dim0 ~dim1 ~ty ~tm =
  (* TODO: case on ty *)
  let tyx = inst_bclo ty @@ into DimGen in
  match out tyx with
  | Univ _ ->
    tm
  | _ ->
    into @@ Coe {dim0; dim1; ty; tm}

and eval_bsys rho sys =
  List.map (eval_btube rho) sys

and eval_btube rho (dim0, dim1, otb) =
  let vdim0 = project_dimval @@ eval rho dim0 in
  let vdim1 = project_dimval @@ eval rho dim1 in
  match Env.compare_dim rho vdim0 vdim1, otb with
  | DimVal.Same, Some tb ->
    Tube.True (tb <:+ rho)
  | DimVal.Apart, _ -> 
    Tube.False (vdim0, vdim1)
  | DimVal.Indeterminate, Some tb ->
    let rho' = Env.restrict_exn rho vdim0 vdim1 in
    Tube.Indeterminate ((vdim0, vdim1), tb <:+ rho')
  | _ -> failwith "eval_tube"

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
    let cod = Clo.PiCodCoe {bclo = info.ty; dim1 = info.dim1; arg = varg} in
    let varg' = rigid_coe ~dim0:info.dim1 ~dim1:info.dim0 ~ty:dom ~tm:varg in
    rigid_coe ~dim0:info.dim0 ~dim1:info.dim1 ~ty:cod ~tm:(apply info.tm varg')

  | HCom info ->
    let dom, cod = out_pi info.ty in
    let vcod = inst_bclo cod varg in
    let vcap = apply info.cap varg in
    let vsys = map_tubes (fun bclo -> Clo.App (bclo, varg)) info.sys in
    rigid_hcom ~dim0:info.dim0 ~dim1:info.dim1 ~ty:vcod ~cap:vcap ~sys:vsys

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
    begin
      match project_sys sys with
      | Some v ->
        rigid_coe ~dim0:info.dim0 ~dim1:info.dim1 ~ty ~tm:v
      | None ->
        let sys' = mapi_tubes (fun i _ -> Clo.ExtSysTube (info.ty, i, vdim)) sys in
        rigid_com ~dim0:info.dim0 ~dim1:info.dim1 ~ty ~cap ~sys:sys'
    end

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
        rigid_hcom ~dim0:info.dim0 ~dim1:info.dim1 ~ty ~cap ~sys:(sys @ info.sys)
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
    rigid_coe ~dim0:info.dim0 ~dim1:info.dim1 ~ty:(Clo.SgDom info.ty) ~tm:vcar

  | HCom info ->
    let dom, _ = out_sg info.ty in
    let ty = eval_clo dom in
    let cap = car info.cap in
    let sys = map_tubes (fun tb -> Clo.Car tb) info.sys in
    rigid_hcom ~dim0:info.dim0 ~dim1:info.dim1 ~ty ~cap ~sys

  | _ -> failwith "car"

and cdr v = 
  match out v with
  | Cons (_, clo) ->
    eval_clo clo

  | Up (vty, vneu) ->
    let dom, cod = out_sg vty in
    let vdom = eval_clo dom in
    let vcar = into @@ Up (vdom, into @@ Car vneu) in
    let vcod = inst_bclo cod vcar in
    into @@ Up (vcod, into @@ Cdr vneu)

  | Coe info ->
    let vcar = car info.tm in
    let vcdr = cdr info.tm in
    let cod = Clo.SgCodCoe {bclo = info.ty; dim0 = info.dim0; arg = vcar} in
    rigid_coe ~dim0:info.dim0 ~dim1:info.dim1 ~ty:cod ~tm:vcdr

  | HCom info ->
    let ty = Clo.SgCodHCom {ty = info.ty; dim0 = info.dim0; cap = info.cap; sys = info.sys} in
    let cap = cdr info.cap in
    let sys = map_tubes (fun bclo -> Clo.Cdr bclo) info.sys in
    rigid_com ~dim0:info.dim0 ~dim1:info.dim1 ~ty ~cap ~sys

  | _ -> failwith "cdr"

and project_bsys sys r =
  match sys with 
  | [] ->
    None
  | Tube.True tb :: sys ->
    Some (inst_bclo tb @@ embed_dimval r)
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

  | Clo.PiCodCoe {bclo; dim1; arg = arg'} ->
    let dom = Clo.PiDom bclo in
    let dimx = project_dimval arg in
    let _, cod = out_pi @@ inst_bclo bclo arg in
    let coe = rigid_coe ~dim0:dim1 ~dim1:dimx ~ty:dom ~tm:arg' in
    inst_bclo cod coe

  | Clo.SgCodCoe {bclo; dim0; arg = arg'} ->
    let dom = Clo.SgDom bclo in
    let dimx = project_dimval arg in
    let _, cod = out_sg @@ inst_bclo bclo arg in
    let coe = rigid_coe ~dim0 ~dim1:dimx ~ty:dom ~tm:arg' in
    inst_bclo cod coe

  | Clo.SgCodHCom {ty; dim0; cap; sys} ->
    let dom, cod = out_sg ty in
    let dimx = project_dimval arg in
    let ty' = eval_clo dom in
    let cap' = car cap in
    let sys' = map_tubes (fun bclo -> Clo.Car bclo) sys in
    let hcom = rigid_hcom ~dim0 ~dim1:dimx ~ty:ty' ~cap:cap' ~sys:sys' in
    inst_bclo cod hcom

  | Clo.ExtCod (bclo, vdim) ->
    let cod, _ = out_ext @@ inst_bclo bclo arg in
    inst_bclo cod @@ embed_dimval vdim

  | Clo.ExtSysTube (bclo, i, arg') ->
    let _, sclo = out_ext @@ inst_bclo bclo arg in
    let sys = inst_sclo sclo arg' in
    eval_clo @@ Tube.proj @@ List.nth sys i

  | Clo.ComCoeTube {bclo; ty; dim1} ->
    let v = inst_bclo bclo arg in
    let dimx = project_dimval arg in
    rigid_coe ~dim0:dimx ~dim1 ~ty ~tm:v

  | Clo.App (bclo, arg') ->
    let v = inst_bclo bclo arg in
    apply v arg'

  | Clo.Car bclo ->
    let v = inst_bclo bclo arg in
    car v

  | Clo.Cdr bclo ->
    let v = inst_bclo bclo arg in
    cdr v

  | Clo.Wk tclo -> 
    eval_clo tclo

and inst_sclo sclo arg = 
  match sclo with
  | Clo.SysAwait {sys = Tm.B sys; env} ->
    let arg' = embed_dimval arg in
    let env' = Env.ext env arg' in
    let go (tdim0, tdim1, otb) =
      let vdim0 = project_dimval @@ eval env' tdim0 in
      let vdim1 = project_dimval @@ eval env' tdim1 in
      match Env.compare_dim env' vdim0 vdim1 with
      | DimVal.Same -> 
        let tm = Option.get_exn otb in
        Tube.True (tm <: env')
      | DimVal.Apart ->
        Tube.False (vdim0, vdim1)
      | DimVal.Indeterminate ->
        let env'' = Env.restrict_exn env' vdim0 vdim1 in
        let tm = Option.get_exn otb in
        Tube.Indeterminate ((vdim0, vdim1), tm <: env'')
    in
    List.map go sys

and eval_clo clo =
  match clo with
  | Clo.Eval {tm; env} ->
    eval env tm

  | Clo.Inst (bclo, arg) ->
    inst_bclo bclo arg


let reflect ty neu = 
  into @@ Up (ty, neu)

let generic ty lvl = 
  reflect ty @@ into @@ Lvl lvl
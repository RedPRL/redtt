module D = DimVal

type tm = Tm.chk Tm.t
type dim = D.t
type query = Eq of dim * dim

type can = [`Can]
type neu = [`Can]
type atom = Symbol.t

module type Perm =
sig
  type t
  val emp : t
  val swap : atom -> atom -> t
  val cmp : t -> t -> t
  val lookup : atom -> t -> atom
  val read : dim -> t -> dim
end

module V (P : Perm) =
struct

  type eqn = D.t * D.t
  type perm = P.t
  type rel = DimRel.t

  type delta =
    | Id
    | Equate of eqn
    | Cmp of delta * delta

  let rec eval_delta delta phi =
    match delta with
    | Id ->
      phi
    | Equate (r, r') ->
      DimRel.restrict_exn phi r r'
    | Cmp (delta1, delta0) ->
      eval_delta delta1 @@
      eval_delta delta0 phi

  module Tube =
  struct
    type 'a t =
      | True of eqn * 'a
      | Indet of eqn * 'a
      | False of eqn
      | Delete
  end

  (* the idea is that for any part of the term in which we may need to issue a dimension substitution,
     we should make it a family [delta -> can t]. This can be easily memoized later so that we don't
     repeatedly evaluate the expression. *)

  (* TODO: now we use a nominal represnetation of dimension binders, so we need swapping. this is currently
     implemented naively, but it should be replaced by suspended permutations. *)

  type _ t =
    | Pi : {dom : can t; cod : clo} -> can t
    | Sg : {dom : can t; cod : clo} -> can t
    | Ext : rst abs -> can t

    | V : {r : dim; ty0 : delta -> can t; ty1 : delta -> can t; equiv : can t fam} -> can t
    | VIn : {r : dim; el0 : can t; el1 : can t} -> can t

    | Coe : {r : dim; r' : dim; abs : can t abs; el : can t} -> can t
    | HCom : {r : dim; r' : dim; ty : can t fam; cap : can t fam; sys : can t abs sys} -> can t
    | FCom : {r : dim; r' : dim; cap : can t fam; sys : can t abs sys} -> can t

    | Lam : clo -> can t
    | Pair : can t * can t -> can t
    | FunApp : neu t * can t -> can t
    | ExtApp : neu t * dim -> can t

    | Univ : Lvl.t -> can t
    | Bool : can t

    | Up : {ty : can t; neu : neu t} -> can t

    | Lvl : int -> neu t

    | Interval : can t

  and 'a cfg = {tm : 'a; phi : rel; rho : env; pi : perm}
  and 'a abs = Symbol.t * 'a
  and 'a fam = delta -> 'a
  and 'a tube = 'a Tube.t
  and 'a sys = 'a fam tube list
  and rst = R of {ty : can t fam; sys : can t sys}
  and clo = B of Tm.chk Tm.t cfg
  and env = env_el list
  and env_el = Val of can t | Dim of D.t

  let out_pi v =
    match v with
    | Pi {dom; cod} -> dom, cod
    | _ -> failwith "out_pi"

  let out_sg v =
    match v with
    | Sg {dom; cod} -> dom, cod
    | _ -> failwith "out_sg"
  let rec act pi v =
    match v with
    | Pi {dom; cod} ->
      Pi {dom = act pi dom; cod = act_clo pi cod}

    | Sg {dom; cod} ->
      Sg {dom = act pi dom; cod = act_clo pi cod}

    | Ext (x, R {ty; sys}) ->
      let rst = R {ty = act_fam pi ty; sys = act_sys pi sys} in
      Ext (P.lookup x pi, rst)

    | V info ->
      let r = P.read info.r pi in
      let ty0 = act_fam pi info.ty0 in
      let ty1 = act_fam pi info.ty1 in
      let equiv = act_fam pi info.equiv in
      V {r; ty0; ty1; equiv}

    | VIn info ->
      let r = P.read info.r pi in
      let el0 = act pi info.el0 in
      let el1 = act pi info.el1 in
      VIn {r; el0; el1}

    | Coe info ->
      let r = P.read info.r pi in
      let r' = P.read info.r' pi in
      let abs = act_abs pi info.abs in
      let el = act pi info.el in
      Coe {r; r'; abs; el}

    | HCom info ->
      failwith "TODO"

    | FCom _ ->
      failwith "TODO"

    | Lam clo ->
      Lam (act_clo pi clo)

    | Pair (v0, v1) ->
      Pair (act pi v0, act pi v1)

    | FunApp (v0, v1) ->
      FunApp (act pi v0, act pi v1)

    | ExtApp (v, r) ->
      ExtApp (act pi v, P.read r pi)

    | Up {ty; neu} ->
      Up {ty = act pi ty; neu = act pi neu}

    | (Bool | Interval | Univ _ | Lvl _) ->
      v

  and act_fam pi fam =
    fun rel -> act pi (fam rel)

  and act_clo pi (B cfg) =
    B {cfg with pi = P.cmp pi cfg.pi}

  and act_abs pi (x, vx) =
    P.lookup x pi, act pi vx

  and act_sys pi sys =
    List.map (act_tube pi) sys

  and act_tube pi tube =
    match tube with
    | Tube.True ((r, r'), fam) ->
      Tube.True ((P.read r pi, P.read r' pi), act_fam pi fam)

    | Tube.Indet ((r, r'), fam) ->
      Tube.Indet ((P.read r pi, P.read r' pi), act_fam pi fam)

    | Tube.False (r, r') ->
      Tube.False (P.read r pi, P.read r' pi)

    | Tube.Delete ->
      Tube.Delete


  let rec eval : type a. a Tm.t cfg -> can t =
    fun cfg ->
      match Tm.out cfg.tm with
      | Tm.Pi (dom, Tm.B (_, cod)) ->
        let dom = eval {cfg with tm = dom} in
        let cod = B {cfg with tm = cod} in
        Pi {dom; cod}

      | Tm.Sg (dom, Tm.B (_, cod)) ->
        let dom = eval {cfg with tm = dom} in
        let cod = B {cfg with tm = cod} in
        Sg {dom; cod}

      | Tm.Lam (Tm.B (_, bdy)) ->
        let bdy = B {cfg with tm = bdy} in
        Lam bdy

      | Tm.FunApp (t0, t1) ->
        let v0 = eval {cfg with tm = t0} in
        let v1 = eval {cfg with tm = t1} in
        apply v0 v1

      | Tm.ExtApp (t0, t1) ->
        let v = eval {cfg with tm = t0} in
        let r = eval_dim {cfg with tm = t1} in
        ext_apply v r

      | Tm.Coe info ->
        let r = eval_dim {cfg with tm = info.dim0} in
        let r' = eval_dim {cfg with tm = info.dim1} in
        let abs =
          lazy begin
            let x = Symbol.fresh () in
            let Tm.B (_, ty) = info.ty in
            x, eval {cfg with tm = ty; rho = Dim (D.Named x) :: cfg.rho}
          end
        in
        let el =
          lazy begin
            eval {cfg with tm = info.tm}
          end
        in
        make_coe r r' abs el

      | Tm.HCom info ->
        let r = eval_dim {cfg with tm = info.dim0} in
        let r' = eval_dim {cfg with tm = info.dim1} in
        let ty = eval_fam {cfg with tm = info.ty} in
        let cap = eval_fam {cfg with tm = info.cap} in
        let sys = eval_bsys {cfg with tm = info.sys} in
        make_hcom r r' ty cap sys

      | Tm.Interval ->
        Interval

      | _ -> failwith ""

  and eval_fam cfg =
    fun delta ->
      eval {cfg with phi = eval_delta delta cfg.phi}

  and eval_bsys cfg =
    List.map
      (fun tube -> eval_btube {cfg with tm = tube})
      cfg.tm

  and eval_btube cfg =
    let tr, tr', otm = cfg.tm in
    let r = eval_dim {cfg with tm = tr} in
    let r' = eval_dim {cfg with tm = tr'} in
    match D.compare r r', otm with
    | D.Same, Some (Tm.B (_, tm)) ->
      let x = Symbol.fresh () in
      let fam = eval_fam {cfg with tm = tm; rho = Dim (D.Named x) :: cfg.rho} in
      let abs = x, fam in
      Tube.True ((r, r'), abs)

    | D.Indeterminate, Some (Tm.B (_, tm)) ->
      let x = Symbol.fresh () in
      let fam = eval_fam {cfg with tm = tm; rho = Dim (D.Named x) :: cfg.rho} in
      let abs = x, fam in
      Tube.Indet ((r, r'), abs)

    | D.Apart, _ ->
      Tube.False (r, r')

    | _ ->
      failwith "eval_tube"

  and eval_dim cfg =
    match Tm.out cfg.tm with
    | Tm.Var i ->
      begin
        match List.nth cfg.rho i with
        | Dim d -> DimRel.canonize cfg.phi d
        | _ -> failwith "Expected dimension in environment"
      end
    | Tm.Dim0 ->
      D.Dim0
    | Tm.Dim1 ->
      D.Dim1
    | _ -> failwith "eval_dim"


  and apply vfun varg =
    match vfun with
    | Lam clo ->
      inst_clo clo varg

    | Coe info ->
      let x, ty = info.abs in
      let dom, cod = out_pi ty in
      let coe_arg s =
        let y = Symbol.fresh () in
        rigid_coe info.r' s (y, act (P.swap x y) dom) varg
      in
      rigid_coe info.r info.r' (x, inst_clo cod @@ coe_arg @@ D.Named x) @@
      apply info.el @@ coe_arg info.r

    | _ ->
      failwith "apply"

  and ext_apply _vext _r =
    failwith "TODO"


  and vin r el0 el1 =
    match r with
    | D.Dim0 ->
      Lazy.force el0
    | D.Dim1 ->
      Lazy.force el1
    | _ ->
      VIn {r; el0 = Lazy.force el0; el1 = Lazy.force el1}



  and make_hcom r r' ty cap sys =
    match D.compare r r' with
    | D.Same ->
      cap Id
    | _ ->
      match project_bsys r' sys with
      | None -> rigid_hcom r r' ty cap sys
      | Some v -> v

  and rigid_hcom _r _r' _ty _cap _sys =
    failwith "TODO"

  and project_bsys r' sys =
    match sys with
    | [] ->
      None

    | Tube.True (_, (x, fam)) :: _ ->
      let v = fam @@ Equate (D.Named x, r') in
      Some v

    | _ :: sys ->
      project_bsys r' sys

  and make_coe r r' abs el =
    match D.compare r r' with
    | D.Same ->
      Lazy.force el
    | _ ->
      rigid_coe r r' (Lazy.force abs) (Lazy.force el)

  and rigid_coe r r' abs el =
    match abs with
    | _, (Pi _ | Sg _) ->
      Coe {r; r'; abs; el}

    | _, (Bool | Univ _) ->
      el

    | x, V info ->
      begin
        match D.compare (D.Named x) info.r, D.compare r D.Dim0 with
        | D.Same, D.Same ->
          vin r' (lazy el) @@ lazy begin
            let equiv_fun0x = car @@ info.equiv @@ Equate (D.Dim0, D.Named x) in
            rigid_coe r r' (x, info.ty1 Id) @@
            apply equiv_fun0x el
          end

        | _ -> failwith "TODO: it gets harder from here ;-)"
      end

    | _ -> failwith "TODO"

  and car v =
    match v with
    | Pair (v0, _) ->
      v0

    | Coe info ->
      let (x, ty) = info.abs in
      let dom, _ = out_sg ty in
      let abs = (x, dom) in
      let el = car info.el in
      rigid_coe info.r info.r' abs el

    | _ ->
      failwith "TODO: car"

  and inst_clo (B cfg) v =
    eval {cfg with rho = Val v :: cfg.rho}


end

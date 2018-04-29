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

  type perm = P.t
  type rel = DimRel.t

  type delta =
    | Id
    | Equate of D.t * D.t
    | Cmp of delta * delta

  (* the idea is that for any part of the term in which we may need to issue a dimension substitution,
     we should make it a family [delta -> can t]. This can be easily memoized later so that we don't
     repeatedly evaluate the expression. *)

  type _ t =
    | Pi : {dom : can t; cod : clo} -> can t
    | Sg : {dom : can t; cod : clo} -> can t

    | V : {r : dim; ty0 : delta -> can t; ty1 : delta -> can t; equiv : delta -> can t} -> can t
    | VIn : {r : dim; el0 : can t; el1 : can t} -> can t

    | Coe : {r : dim; r' : dim; abs : Symbol.t * can t; el : can t} -> can t

    | Lam : clo -> can t
    | Pair : can t * can t -> can t
    | FunApp : neu t * can t -> can t
    | ExtApp : neu t * dim -> can t

    | Up : {ty : can t; neu : neu t} -> can t

    | Lvl : int -> neu t

    | Interval : can t
    | Dim0 : can t
    | Dim1 : can t
    | DimDelete : can t
    | DimNamed : Symbol.t -> can t

  and 'a cfg = { tm : 'a Tm.t; phi : rel; rho : env; pi : perm}
  and clo = B of Tm.chk cfg
  and env = can t list

  let out_pi v =
    match v with
    | Pi {dom; cod} -> dom, cod
    | _ -> failwith "out_pi"

  let rec act pi v =
    match v with
    | Pi {dom; cod} ->
      Pi {dom = act pi dom; cod = act_clo pi cod}

    | V info ->
      let r = P.read info.r pi in
      let ty0 = act_fam pi info.ty0 in
      let ty1 = act_fam pi info.ty1 in
      let equiv = act_fam pi info.equiv in
      V {r; ty0; ty1; equiv}

    | Coe info ->
      let r = P.read info.r pi in
      let r' = P.read info.r' pi in
      let abs = act_abs pi info.abs in
      let el = act pi info.el in
      Coe {r; r'; abs; el}

    | Lam clo ->
      Lam (act_clo pi clo)

    | _ ->
      failwith ""

  and act_fam pi fam =
    fun rel -> act pi (fam rel)

  and act_clo pi (B cfg) =
    B {cfg with pi = P.cmp pi cfg.pi}

  and act_abs pi (x, vx) =
    P.lookup x pi, act pi vx

  let project_dim (type a) (v : a t) =
    match v with
    | Dim0 -> DimVal.Dim0
    | Dim1 -> DimVal.Dim1
    | Up {ty; neu} ->
      begin
        match ty, neu with
        | Interval, Lvl i -> DimVal.Lvl i
        | _ -> failwith "project_dim/Up"
      end
    | DimDelete -> DimVal.Delete
    | DimNamed x -> DimVal.Named x
    | _ ->
      failwith "project_dim"

  let rec eval : type a. a cfg -> can t =
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

      | Tm.Coe info ->
        let r = eval_dim {cfg with tm = info.dim0} in
        let r' = eval_dim {cfg with tm = info.dim1} in
        let abs =
          lazy begin
            let x = Symbol.fresh () in
            let Tm.B (_, ty) = info.ty in
            x, eval {cfg with tm = ty; rho = DimNamed x :: cfg.rho}
          end
        in
        let el =
          lazy begin
            eval {cfg with tm = info.tm}
          end
        in
        make_coe r r' abs el

      | _ -> failwith ""

  and eval_dim cfg =
    DimRel.canonize cfg.phi @@
    project_dim @@
    eval cfg

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


  and vin r el0 el1 =
    match r with
    | D.Dim0 -> Lazy.force el0
    | D.Dim1 -> Lazy.force el1
    | _ -> VIn {r; el0 = Lazy.force el0; el1 = Lazy.force el1}


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

  and car v = failwith ""

  (* match abs with
     | _, Pi _ ->
     M.ret @@ Coe {r; r'; abs; el}

     | x, V info ->
     begin
      M.Dim.ask (D.Named x) info.r @@ function
      | D.Same ->
        begin
          M.Dim.ask r D.Dim0 @@ function
          | D.Same ->
            info.ty1 >>= fun vty1 ->
            M.Dim.restrict D.Dim0 (D.Named x) info.equiv >>= fun vequiv0 ->
            car vequiv0 >>= fun vcar ->
            apply vcar el >>= fun vapp ->
            rigid_coe r r' (x, vty1) vapp >>= fun vcoe ->
            M.ret @@ VIn (r', el, vcoe)

          | _ ->
            failwith ""
        end
      | _ ->
        failwith "TODO"
     end *)



  and inst_clo (B cfg) v =
    eval {cfg with rho = v :: cfg.rho}


end

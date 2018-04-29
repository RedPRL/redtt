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
  type delta = rel -> rel

  type _ t =
    | Pi : {dom : can t; cod : clo} -> can t
    | Sg : {dom : can t; cod : clo} -> can t

    | V : {r : dim; ty0 : delta -> can t; ty1 : delta -> can t; equiv : delta -> can t} -> can t
    | VIn : dim * can t * can t -> can t

    | Coe : {r : dim; r' : dim; abs : Symbol.t * can t; el : can t} -> can t

    | Lam : clo -> can t
    | Pair : can t * can t -> can t
    | FunApp : neu t * can t -> can t
    | ExtApp : neu t * dim -> can t

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

      | _ -> failwith ""

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


  and rigid_coe r r' abs el =
    match abs with
    | _, (Pi _ | Sg _) ->
      Coe {r; r'; abs; el}

    | x, V info ->
      begin
        match D.compare (D.Named x) info.r, D.compare r D.Dim0 with
        | D.Same, D.Same ->
          let vty1 = info.ty1 (fun rel -> rel) in
          let equiv_fun0x = car @@ info.equiv @@ fun rel -> DimRel.restrict_exn rel D.Dim0 (D.Named x) in
          let vapp = apply equiv_fun0x el in
          let vcoe = rigid_coe r r' (x, vty1) vapp in
          VIn (r', el, vcoe)

        | _ -> failwith ""
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

module D = DimVal

type tm = Tm.chk Tm.t
type dim = D.t

type can = [`Can]
type neu = [`Neu]
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


type eqn = D.t * D.t
type rel = DimRel.t

type delta =
  | Id
  | Equate of eqn
  | Cmp of delta * delta

module type Fam =
sig
  type 'a t
  val make : (delta -> 'a) -> 'a t
  val inst : delta -> 'a t -> 'a

  val restrict : delta -> 'a t -> 'a t
end

module V (P : Perm) (F : Fam) =
struct
  type perm = P.t

  let rec eval_delta delta phi =
    match delta with
    | Id ->
      phi
    | Equate (r, r') ->
      DimRel.restrict_exn phi r r'
    | Cmp (delta1, delta0) ->
      eval_delta delta1 @@
      eval_delta delta0 phi

  type 'a tube =
    | True of eqn * 'a
    | Indet of eqn * 'a
    | False of eqn
    | Delete

  type _ f =
    | Pi : {dom: can t; cod : clo} -> can f
    | Sg : {dom: can t; cod : clo} -> can f
    | Lam : clo -> can f

    | Coe : {r : dim t; r' : dim t; abs : can t abs; el : can t} -> can f
    | HCom : {r : dim t; r' : dim t; ty : can t; cap : can t; sys : can t abs sys} -> can f

    | Bool : can f

    | Dim : D.t -> dim f

  and 'a t = 'a f F.t

  and 'a abs = atom * 'a
  and 'a cfg = {tm : 'a; phi : rel; rho : env}
  and 'a sys = 'a tube F.t list
  and clo = Tm.chk Tm.t Tm.bnd cfg
  and env_el = Val of can t | Atom of atom
  and env = env_el list

  let fam_of_dim r =
    F.make @@ fun dl ->
    Dim (DimRel.canonize (eval_delta dl DimRel.emp) r)

  let restrict = F.restrict

  let restrict_sys dl =
    List.map (restrict dl)

  let restrict_clo dl {tm; phi; rho} =
    {tm; phi = eval_delta dl phi; rho}

  let out_pi v =
    match v with
    | Pi {dom; cod} -> dom, cod
    | _ -> failwith "out_pi"


  let act : type a. P.t -> a t -> a t =
    fun _pi ->
      failwith "TODO: act"

  let rec eval : type a. a Tm.t cfg -> can t =
    fun cfg ->
      match Tm.out cfg.tm with
      | Tm.Pi (dom, cod) ->
        F.make @@ fun dl ->
        let dom = restrict dl @@ eval {cfg with tm = dom} in
        let cod = restrict_clo dl @@ {cfg with tm = cod} in
        Pi {dom; cod}

      | Tm.Sg (dom, cod) ->
        F.make @@ fun dl ->
        let dom = restrict dl @@ eval {cfg with tm = dom} in
        let cod = restrict_clo dl @@ {cfg with tm = cod} in
        Sg {dom; cod}

      | Tm.Coe info ->
        let r = eval_dim {cfg with tm = info.dim0} in
        let r' = eval_dim {cfg with tm = info.dim1} in
        let el = eval {cfg with tm = info.tm} in

        let x = Symbol.fresh () in
        let Tm.B (_, tty) = info.ty in
        let abs = x, eval {cfg with tm = tty; rho = Atom x :: cfg.rho} in
        make_coe r r' abs el

      | Tm.HCom info ->
        let r = eval_dim {cfg with tm = info.dim0} in
        let r' = eval_dim {cfg with tm = info.dim1} in
        let ty = eval {cfg with tm = info.ty} in
        let cap = eval {cfg with tm = info.cap} in
        let sys = eval_bsys {cfg with tm = info.sys} in
        make_hcom r r' ty cap sys

      | Tm.FunApp (t0, t1) ->
        let vfun = eval {cfg with tm = t0} in
        let varg = eval {cfg with tm = t1} in
        apply vfun varg

      | Tm.Var i ->
        F.make @@ fun dl ->
        begin
          (* TODO: do I need to do something with cfg.phi here? *)
          match List.nth cfg.rho i with
          | Val v -> F.inst dl v
          | _ -> failwith "Expected value in environment"
        end

      | _ -> failwith ""


  and eval_dim : type a. a Tm.t cfg -> dim t =
    fun cfg ->
      F.make @@ fun dl ->
      match Tm.out cfg.tm with
      | Tm.Dim0 -> Dim Dim0
      | Tm.Dim1 -> Dim Dim1
      | Tm.Var ix ->
        begin
          match List.nth cfg.rho ix with
          | Atom x ->
            let phi = eval_delta dl cfg.phi in
            let dim = DimRel.canonize phi @@ D.Named x in
            Dim dim
          | _ ->
            failwith "Expected atom in environment"
        end
      | _ ->
        failwith "eval_dim"

  and eval_bsys cfg : can t abs sys =
    List.map
      (fun tb -> eval_btube {cfg with tm = tb})
      cfg.tm

  and eval_btube cfg =
    let tr, tr', otm = cfg.tm in
    let r = eval_dim {cfg with tm = tr} in
    let r' = eval_dim {cfg with tm = tr'} in

    F.make @@ fun dl ->
    let Dim r = F.inst dl r in
    let Dim r' = F.inst dl r' in

    match D.compare r r', otm with
    | D.Same, Some (Tm.B (_, tm)) ->
      let x = Symbol.fresh () in
      let abs = x, restrict dl @@ eval {cfg with tm; rho = Atom x :: cfg.rho} in
      True ((r, r'), abs)

    | D.Indeterminate, Some (Tm.B (_, tm)) ->
      let x = Symbol.fresh () in
      let abs = x, restrict dl @@ eval {cfg with tm; rho = Atom x :: cfg.rho} in
      Indet ((r, r'), abs)

    | D.Apart, _ ->
      False (r, r')

    | _ -> failwith "eval_tube"

  and apply vfun varg =
    F.make @@ fun dl ->
    let varg' = restrict dl varg in
    match F.inst dl vfun with
    | Lam clo ->
      let Tm.B (_, bdy) = clo.tm in
      F.inst Id @@
      eval {clo with tm = bdy; rho = Val varg' :: clo.rho}

    | Coe info ->
      let x, tyx = info.abs in
      let dom, cod = out_pi @@ F.inst dl tyx in
      let abs_cod =
        let y = Symbol.fresh () in
        let abs = y, act (P.swap x y) dom in
        let coe = make_coe info.r' (fam_of_dim @@ D.Named x) abs varg' in
        let Tm.B (_, cod_bdy) = cod.tm in
        x, eval {cod with tm = cod_bdy; rho = Val coe :: cod.rho}
      in
      let el = apply info.el @@ make_coe info.r' info.r (x, dom) varg' in
      F.inst Id @@ make_coe info.r info.r' abs_cod el

    | HCom info ->
      F.inst Id @@ make_hcom info.r info.r' (failwith "") (failwith "") (failwith "")

    | _ ->
      failwith ""

  and make_coe r r' (x, tyx) el =
    F.make @@ fun dl ->
    match D.compare (test_dim dl r) (test_dim dl r') with
    | Same -> F.inst dl el
    | _ ->
      match F.inst dl tyx with
      | Bool ->
        F.inst dl el

      | (Pi _ | Sg _) ->
        let abs = x, restrict dl tyx in
        let el = restrict dl el in
        Coe {r; r'; abs; el}

      | _ ->
        failwith "TODO: make_coe"

  and test_dim dl r =
    let Dim r = F.inst dl r in
    r

  and make_hcom r r' ty cap sys =
    F.make @@ fun dl ->
    match D.compare (test_dim dl r) (test_dim dl r') with
    | D.Same ->
      F.inst dl cap
    | _ ->
      match project_bsys dl r' sys with
      | Some v -> v
      | None ->
        match F.inst dl ty with
        | Bool ->
          F.inst dl cap

        | (Pi _ | Sg _) ->
          let ty = restrict dl ty in
          let cap = restrict dl cap in
          let sys = restrict_sys dl sys in
          HCom {r; r'; ty; cap; sys}

        | _ ->
          failwith "TODO: make_hcom"

  and project_bsys dl r' sys =
    match sys with
    | [] ->
      None

    | tube :: sys ->
      match F.inst dl tube with
      | True (_, (y, vy)) ->
        let vr' = F.inst dl @@ restrict (Equate (D.Named y, test_dim dl r')) vy
        in Some vr'

      | _ ->
        project_bsys dl r' sys

end

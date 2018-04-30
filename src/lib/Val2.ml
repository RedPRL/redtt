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
  val map : (delta -> delta) -> 'a t -> 'a t
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
    | Coe : {r : dim; r' : dim; abs : can t abs; el : can t} -> can f
    | HCom : {r : dim; r' : dim; ty : can t; cap : can t; sys : can t abs sys} -> can f

    | Bool : can f

    | Dim : D.t -> dim f

  and 'a t = 'a f F.t

  and 'a abs = atom * 'a
  and 'a cfg = {tm : 'a; phi : rel; rho : env; atoms : atom list}
  and 'a sys = 'a tube F.t list
  and clo = Tm.chk Tm.t Tm.bnd cfg
  and env = can t list

  let fam_of_dim r =
    F.make @@ fun dl ->
    DimRel.canonize (eval_delta dl DimRel.emp) r

  let restrict dl  =
    F.map (fun dl' -> Cmp (dl, dl'))

  let restrict_clo dl {tm; phi; rho; atoms} =
    {tm; phi = eval_delta dl phi; rho; atoms}


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
        let abs = x, eval {cfg with tm = tty; atoms = x :: cfg.atoms} in
        make_coe r r' abs el

      | Tm.HCom info ->
        let r = eval_dim {cfg with tm = info.dim0} in
        let r' = eval_dim {cfg with tm = info.dim1} in
        let ty = eval {cfg with tm = info.ty} in
        let cap = eval {cfg with tm = info.cap} in
        let sys = eval_bsys {cfg with tm = info.sys} in
        make_hcom r r' ty cap sys

      | _ -> failwith ""


  and eval_dim : type a. a Tm.t cfg -> dim t =
    fun cfg ->
      F.make @@ fun dl ->
      match Tm.out cfg.tm with
      | Tm.Dim0 -> Dim Dim0
      | Tm.Dim1 -> Dim Dim1
      | Tm.Var ix ->
        let x = List.nth cfg.atoms ix in
        let phi = eval_delta dl cfg.phi in
        let dim = DimRel.canonize phi @@ D.Named x in
        Dim dim
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
      let abs = x, restrict dl @@ eval {cfg with tm} in
      True ((r, r'), abs)

    | D.Indeterminate, Some (Tm.B (_, tm)) ->
      let x = Symbol.fresh () in
      let abs = x, restrict dl @@ eval {cfg with tm} in
      Indet ((r, r'), abs)

    | D.Apart, _ ->
      False (r, r')

    | _ -> failwith "eval_tube"

  and make_coe r r' (x, tyx) el =
    F.make @@ fun dl ->
    let Dim r = F.inst dl r in
    let Dim r' = F.inst dl r' in
    match D.compare r r' with
    | Same -> F.inst dl el
    | _ ->
      match F.inst dl tyx with
      | Bool -> F.inst dl el
      | (Pi _ | Sg _) ->
        let abs = x, restrict dl tyx in
        let el = restrict dl el in
        Coe {r; r'; abs; el}
      | _ -> failwith ""

  and make_hcom r r' ty cap sys =
    F.make @@ fun dl ->
    let Dim r = F.inst dl r in
    let Dim r' = F.inst dl r' in
    match D.compare r r' with
    | D.Same ->
      F.inst dl cap
    | _ ->
      let rec go sys =
        match sys with
        | [] ->
          rigid_hcom r r' ty cap sys
        | tube :: sys ->
          go_tube (F.inst dl tube) sys
      and go_tube tb sys =
        match tb with
        | True (_, (y, vy)) ->
          F.inst dl @@ restrict (Equate (D.Named y, r')) vy
        | _ ->
          go sys
      in
      go sys

  and rigid_hcom r r' ty cap sys =
    failwith ""


end

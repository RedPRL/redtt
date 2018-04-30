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

module Fam : Fam =
struct
  type 'a t = delta -> 'a
  let make f = f
  let inst dl f = f dl
  let map g f dl = f (g dl)
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

  module Tube =
  struct
    type 'a t =
      | True of eqn * 'a
      | Indet of eqn * 'a
      | False of eqn
      | Delete
  end

  type _ f =
    | Pi : {dom: can t; cod : clo} -> can f
    | Sg : {dom: can t; cod : clo} -> can f
    | Lam : clo -> can f
    | Coe : {r : dim; r' : dim; abs : can t abs; el : can t} -> can f

    | Bool : can f

    | Dim : D.t -> dim f

  and 'a t = 'a f F.t

  and 'a abs = atom * 'a
  and 'a cfg = {tm : 'a; phi : rel; rho : env; atoms : Symbol.t list}
  and clo = Tm.chk Tm.t Tm.bnd cfg
  and env = can t list

  let restrict r r'  =
    F.map (fun dl -> Cmp (Equate (r, r'), dl))

  let restrict_clo r r' {tm; phi; rho; atoms} =
    {tm; phi = DimRel.restrict_exn phi r r'; rho; atoms}


  let rec eval : type a. a Tm.t cfg -> can t =
    fun cfg ->
      match Tm.out cfg.tm with
      | Tm.Pi (dom, cod) ->
        F.make @@ fun dl ->
        let phi = eval_delta dl cfg.phi in
        let dom = eval {cfg with tm = dom; phi} in
        let cod = {cfg with tm = cod; phi} in
        Pi {dom; cod}

      | Tm.Sg (dom, cod) ->
        F.make @@ fun dl ->
        let phi = eval_delta dl cfg.phi in
        let dom = eval {cfg with tm = dom; phi} in
        let cod = {cfg with tm = cod; phi} in
        Sg {dom; cod}

      | Tm.Coe info ->
        let r = eval_dim {cfg with tm = info.dim0} in
        let r' = eval_dim {cfg with tm = info.dim1} in
        let Tm.B (_, ty) = info.ty in
        let x = Symbol.fresh () in
        let vty = eval {cfg with tm = ty; atoms = x :: cfg.atoms} in
        make_coe r r' (x, vty) @@
        eval {cfg with tm = info.tm}

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


  and make_coe r r' (x, ty) el =
    F.make @@ fun dl ->
    let Dim r = F.inst dl r in
    let Dim r' = F.inst dl r' in
    match D.compare r r' with
    | D.Same ->
      F.inst dl el
    | _ ->
      F.inst dl @@ rigid_coe r r' (x, ty) el

  and rigid_coe r r' (x, ty) el =
    F.make @@ fun dl ->
    match F.inst dl ty with
    | Bool ->
      F.inst dl el
    | (Pi _ | Sg _) ->
      Coe {r; r'; abs = (x, ty); el}
    | _ ->
      failwith "rigid_coe"


end

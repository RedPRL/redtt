module D = DimVal

type tm = Tm.chk Tm.t
type dim = D.t

type can = [`Can]
type neu = [`Neu]
type atom = Symbol.t


type eqn = D.t * D.t
type perm = Permutation.t
type rst = Restriction.t

module type Fam =
sig
  type 'a t
  val make : (rst -> 'a) -> 'a t
  val inst : rst -> 'a t -> 'a

  val restrict : rst -> 'a t -> 'a t
end

module V (F : Fam) =
struct
  module P = Permutation
  module R = Restriction

  type 'a tube =
    | True of eqn * 'a
    | Indet of eqn * 'a
    | False of eqn
    | Delete

  (* What is very unclear to me is what dimension variable values mean, or what it means to evaluate one.
     That is, how do I compare two elements of type 'dim t'? I think that somehow canonizing them is not enough,
     but I cannot quite put my finger on why that is not correct. *)


  type _ f =
    | Pi : {dom: can t; cod : clo} -> can f
    | Sg : {dom: can t; cod : clo} -> can f
    | Lam : clo -> can f

    | Coe : {r : dim t; r' : dim t; abs : can t abs; el : can t} -> can f
    | HCom : {r : dim t; r' : dim t; ty : can t; cap : can t; sys : can t abs sys} -> can f

    | Bool : can f

    | Dim : D.t -> dim f

  and 'a t = 'a f F.t

  and 'a abs = B of atom * 'a
  and 'a cfg = {tm : 'a; phi : rst; rho : env}
  and 'a sys = 'a tube F.t list
  and clo = Tm.chk Tm.t Tm.bnd cfg
  and env_el = Val of can t | Atom of atom
  and env = env_el list

  let restrict = F.restrict

  let restrict_sys phi =
    List.map (restrict phi)

  let restrict_clo psi clo =
    {clo with phi = R.union psi clo.phi}

  let out_pi v =
    match v with
    | Pi {dom; cod} -> dom, cod
    | _ -> failwith "out_pi"


  let rec act : type a. P.t -> a t -> a t =
    fun pi fam ->
      F.make @@ fun phi ->
      F.inst (R.perm pi phi) fam

  and act_clo pi clo =
    {clo with phi = R.perm pi clo.phi}

  and unleash abs =
    let B (y, v) = abs in
    let x = Symbol.fresh () in
    x, act (P.swap y x) v

  module Val =
  struct
    let coe r r' abs m =
      failwith ""
  end

  module Sem =
  struct
    let pi dom cod =
      F.make @@ fun phi ->
      Pi {dom = restrict phi dom; cod = restrict_clo phi cod}
  end

  let rec eval cfg =
    match Tm.out cfg.tm with
    | Tm.Pi (dom, cod) ->
      let dom = eval {cfg with tm = dom} in
      let cod = {cfg with tm = cod} in
      Sem.pi dom cod

    | _ ->
      failwith "TODO"


end

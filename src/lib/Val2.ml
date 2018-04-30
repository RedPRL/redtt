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


  type _ f =
    | Pi : {dom: can t; cod : clo} -> can f
    | Sg : {dom: can t; cod : clo} -> can f
    | Lam : clo -> can f
    | Coe : {r : dim; r' : dim; abs : can t abs; el : can t} -> can f

  and 'a t = Node of {con : delta -> 'a f}
  and 'a abs = atom * 'a
  and 'a cfg = {tm : 'a; phi : rel; rho : env; pi : perm}
  and clo = Tm.chk Tm.t Tm.bnd cfg
  and env = can t list


  let rec out (Node node) dl =
    node.con dl

  let into fam =
    Node {con = fam}

  let restrict r r' (Node node) =
    Node {con = fun dl -> node.con @@ Cmp (Equate (r, r'), dl)}

  let restrict_clo r r' {tm; phi; rho; pi} =
    {tm; phi = DimRel.restrict_exn phi r r'; rho; pi}


  let rec eval : type a. a Tm.t cfg -> can t =
    fun cfg ->
      match Tm.out cfg.tm with
      | Tm.Pi (dom, cod) ->
        into @@ fun dl ->
        let phi = eval_delta dl cfg.phi in
        let dom = eval {cfg with tm = dom; phi} in
        let cod = {cfg with tm = cod; phi} in
        Pi {dom; cod}

      | Tm.Sg (dom, cod) ->
        into @@ fun dl ->
        let phi = eval_delta dl cfg.phi in
        let dom = eval {cfg with tm = dom; phi} in
        let cod = {cfg with tm = cod; phi} in
        Sg {dom; cod}

      | _ -> failwith ""


end

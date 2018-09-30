open RedBasis
open Bwd
module D = NewDomain
module Rel = NewRestriction

exception PleaseFillIn
exception PleaseRaiseProperError
exception CanJonHelpMe
exception CanFavoniaHelpMe

module Env :
sig
  type t

  val emp : unit -> t (* maybe just [emp : t]? *)
  val fresh : t -> int * t
  val abs : Name.t bwd -> t -> t
  val abs1 : Name.t -> t -> t

  val ix_of_lvl : int -> t -> int
  val ix_of_atom : Name.t -> t -> int (* might throw Not_found *)
end =
struct
  module M = Map.Make (Name)
  type t = {n_minus_one : int; atoms : int M.t}

  let emp () = {n_minus_one = -1; atoms = M.empty}

  let fresh env =
    let n = env.n_minus_one + 1 in
    n, {env with n_minus_one = n}

  let abs1 x env =
    let lvl, env = fresh env in
    {env with atoms = M.add x lvl env.atoms}

  let abs xs env =
    Bwd.fold_left (fun env x -> abs1 x env) env xs

  let ix_of_lvl l env =
    env.n_minus_one - l

  let ix_of_atom x env =
    let lvl = M.find x env.atoms in
    ix_of_lvl lvl env
end

type rel = Rel.t
type env = Env.t

(* maybe we should just [open D]? *)
type value = D.value
type neu = D.neu
type 'a face = 'a D.face
type 'a sys = 'a D.sys

module Q :
sig
  val equate_dim : env -> rel -> I.t -> I.t -> Tm.tm
  (* favonia: whether these should take a D.value or D.con as arguments will hopefully be clear in the future. *)
  val equate_nf : env -> rel -> value -> value -> value -> Tm.tm
  val equate_neu : env -> rel -> neu -> neu -> Tm.tm Tm.cmd
  val equate_ty : env -> rel -> value -> value -> Tm.tm
  val equate_val_sys : env -> rel -> value -> value sys -> value sys -> (Tm.tm, Tm.tm) Tm.system

  val subtype : env -> rel -> value -> value -> unit
end =
struct
  let ignore _ = ()

  let quote_dim env =
    function
    | `Dim0 -> Tm.make Tm.Dim0
    | `Dim1 -> Tm.make Tm.Dim1
    | `Atom x ->
      match Env.ix_of_atom x env with
      | ix -> Tm.up @@ Tm.ix ix
      | exception Not_found -> Tm.up @@ Tm.var x

  let equate_dim env rel r0 r1 =
    match Rel.compare r0 r1 rel with
    | `Same -> quote_dim env r0
    | _ -> raise PleaseRaiseProperError

  let rec equate_nf _ = raise PleaseFillIn
  and equate_neu _ = raise PleaseFillIn
  and equate_ty _ = raise PleaseFillIn
  and equate_val_sys _ = raise PleaseFillIn

  and subtype env rel ty0 ty1 =
    ignore @@ equate_ty env rel ty0 ty1;
    raise CanJonHelpMe
end

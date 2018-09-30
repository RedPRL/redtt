open RedBasis
open Bwd
module D = NewDomain

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
  val ix_of_atom : Name.t -> t -> int
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
    match M.find x env.atoms with
    | lvl -> ix_of_lvl lvl env
    | exception Not_found ->
      raise PleaseRaiseProperError
end

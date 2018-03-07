type 'a b = B of 'a

type chk =
  | Up of inf
  | Unit
  | Bool
  | Pi of chk * chk b
  | Sg of chk * chk b
  | Eq of chk b * chk * chk
  | Lam of chk b
  | Pair of chk * chk
  | Ax
  | Tt
  | Ff
  | Dim0
  | Dim1
  | U of int

and inf =
  | Var of int
  | App of inf * chk
  | Proj1 of inf
  | Proj2 of inf
  | If of chk b * inf * chk * chk
  | Down of chk * chk

module Pretty =
struct
  type 'a t = Format.formatter -> 'a -> unit

  module Env : 
  sig
    type t
    val emp : t
    val var : int -> t -> string
    val bind : t -> string * t
  end = 
  struct
    type t = int * string list

    let emp = 0, []
    let var i (_, xs) = List.nth xs i
    let bind (i, xs) =
      let x = "_" ^ string_of_int i in 
      x, (i + 1, x :: xs)
  end

  let rec pp_chk rho fmt t = 
    match t with
    | Up t ->
      Format.fprintf fmt "%a" (pp_inf rho) t

    | Unit ->
      Format.fprintf fmt "unit"

    | Bool ->
      Format.fprintf fmt "bool"

    | U i -> 
      Format.fprintf fmt "(U %i)" i

    | Pi (dom, B cod) ->
      let x, rho' = Env.bind rho in
      Format.fprintf fmt "(-> %a [%s] %a)" (pp_chk rho) dom x (pp_chk rho') cod

    | Sg (dom, B cod) ->
      let x, rho' = Env.bind rho in 
      Format.fprintf fmt "(* %a [%s] %a)" (pp_chk rho) dom x (pp_chk rho') cod

    | Eq (B cod, t1, t2) -> 
      let x, rho' = Env.bind rho in
      Format.fprintf fmt "(eq [%s] %a %a %a)" x (pp_chk rho') cod (pp_chk rho) t1 (pp_chk rho) t2

    | Lam (B t) ->
      let x, rho' = Env.bind rho in
      Format.fprintf fmt "(lam [%s] %a)" x (pp_chk rho') t

    | Pair (t1, t2) -> 
      Format.fprintf fmt "(cons %a %a)" (pp_chk rho) t1 (pp_chk rho) t2

    | Ax -> 
      Format.fprintf fmt "ax"

    | Tt -> 
      Format.fprintf fmt "tt"

    | Ff -> 
      Format.fprintf fmt "ff"

    | Dim0 -> 
      Format.fprintf fmt "0"

    | Dim1 -> 
      Format.fprintf fmt "1"

  and pp_inf rho fmt r =
    match r with
    | Var i ->
      Format.fprintf fmt "%s" @@ Env.var i rho

    | App (r, t) ->
      Format.fprintf fmt "(app %a %a)" (pp_inf rho) r (pp_chk rho) t

    | Proj1 r ->
      Format.fprintf fmt "(car %a)" (pp_inf rho) r

    | Proj2 r ->
      Format.fprintf fmt "(cdr %a)" (pp_inf rho) r

    | If (B mot, r, t1, t2) ->
      let x, rho' = Env.bind rho  in
      Format.fprintf fmt "(if [%s] %a %a %a %a)" x (pp_chk rho') mot (pp_inf rho) r (pp_chk rho) t1 (pp_chk rho) t2

    | Down (ty, t) -> 
      Format.fprintf fmt "(: %a %a)" (pp_chk rho) ty (pp_chk rho) t
end
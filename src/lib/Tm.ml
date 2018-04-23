type 'a bnd = B of 'a

type chk = [`Chk]
type inf = [`Inf]

type info = Lexing.position * Lexing.position

type _ f =
  | Var : int -> inf f
  | Car : inf t -> inf f
  | Cdr : inf t -> inf f
  | FunApp : inf t * chk t -> inf f
  | ExtApp : inf t * chk t -> inf f

  | Down : {ty : chk t; tm : chk t} -> inf f
  | Coe : {dim0 : chk t; dim1 : chk t; ty : chk t bnd; tm : chk t} -> inf f
  | HCom : {dim0 : chk t; dim1 : chk t; ty : chk t; cap : chk t; sys : chk t bnd system} -> inf f
  | Com : {dim0 : chk t; dim1 : chk t; ty : chk t bnd; cap : chk t; sys : chk t bnd system} -> inf f  

  | Up : inf t -> chk f

  | Univ : Lvl.t -> chk f
  | Pi : chk t * chk t bnd -> chk f
  | Ext : (chk t * chk t system) bnd -> chk f
  | Sg : chk t * chk t bnd -> chk f
  | Interval : chk f

  | Bool : chk f
  | Tt : chk f
  | Ff : chk f
  | If : {mot : chk t bnd; scrut : inf t; tcase : chk t; fcase : chk t} -> inf f

  | Lam : chk t bnd -> chk f
  | Cons : chk t * chk t -> chk f
  | Dim0 : chk f
  | Dim1 : chk f

  | Let : inf t * chk t bnd -> chk f
  | Meta : Symbol.t * subst -> inf f

and subst = 
  | Id
  | Proj
  | Sub of subst * inf t
  | Cmp of subst * subst

and 'a node = {info : info option; con : 'a f}
and 'a t = 'a node
and 'a tube = chk t * chk t * 'a option
and 'a system = 'a tube list

let into tf = {info = None; con = tf}
let into_info info tf = {info = info; con = tf}
let info node = node.info

let out node = node.con

module Pretty =
struct
  module Env :
  sig
    type t
    val emp : t
    val var : int -> t -> string
    val bind : string -> t -> t
    val bind_fresh : t -> string * t
  end =
  struct
    type t = int * string list

    let emp = 0, []
    let var i (_, xs) = List.nth xs i
    let bind_fresh (i, xs) =
      let x = "x" ^ string_of_int i in
      x, (i + 1, x :: xs)

    let bind nm (i, xs) =
      (i, nm :: xs)
  end

  let rec pp : type a. Env.t -> Format.formatter -> a t -> unit = 
    fun env fmt tm ->
      match out tm with
      | Var i -> 
        Format.fprintf fmt "%s" @@ 
        Env.var i env

      | Down {ty; tm} ->
        Format.fprintf fmt "@[<1>(:>@ %a@ %a)@]" (pp env) ty (pp env) tm

      | Pi (dom, B cod) ->
        let x, env' = Env.bind_fresh env in
        Format.fprintf fmt "@[<1>(-> [%s : %a]@ %a)@]" x (pp env) dom (pp env') cod

      | Sg (dom, B cod) ->
        let x, env' = Env.bind_fresh env in
        Format.fprintf fmt "@[<1>(* [%s : %a]@ %a)@]" x (pp env) dom (pp env') cod

      | Ext (B (cod, sys)) ->
        let x, env' = Env.bind_fresh env in
        begin
          match sys with
          | [] ->
            Format.fprintf fmt "@[<1>(# [%s]@ %a)@]" x (pp env') cod
          | _ ->
            Format.fprintf fmt "@[<1>(# [%s]@ %a@ %a)@]" x (pp env') cod (pp_sys env') sys
        end

      | Lam (B tm) ->
        let x, env' = Env.bind_fresh env in
        Format.fprintf fmt "@[<1>(lam [%s]@ %a)@]" x (pp env') tm

      | FunApp (tm0, tm1) ->
        Format.fprintf fmt "@[<1>(%a@ %a)@]" (pp env) tm0 (pp env) tm1

      | ExtApp (tm0, tm1) ->
        Format.fprintf fmt "@[<1>(%s %a@ %a)@]" "@" (pp env) tm0 (pp env) tm1

      | Up tm ->
        pp env fmt tm

      | Bool ->
        Format.fprintf fmt "bool"

      | Interval ->
        Format.fprintf fmt "dim"

      | Tt ->
        Format.fprintf fmt "tt"

      | Ff ->
        Format.fprintf fmt "ff"

      | Dim0 ->
        Format.fprintf fmt "0"

      | Dim1 ->
        Format.fprintf fmt "1"

      | Univ lvl ->
        Format.fprintf fmt "(U %a)" Lvl.pp lvl

      | _ ->
        Format.fprintf fmt "<term>"

  and pp_sys env fmt sys = 
    match sys with
    | [] ->
      ()
    
    | [tube] ->
      pp_tube env fmt tube

    | tube :: sys ->
      Format.fprintf fmt "%a@ %a" (pp_tube env) tube (pp_sys env) sys

  and pp_tube env fmt tube = 
    let dim0, dim1, otm = tube in
    match otm with
    | None -> 
      Format.fprintf fmt "@[<1>[%a=%a@ -]@]" (pp env) dim0 (pp env) dim1

    | Some tm -> 
      Format.fprintf fmt "@[<1>[%a=%a@ %a]@]" (pp env) dim0 (pp env) dim1 (pp env) tm
end
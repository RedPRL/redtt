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
    val bind : t -> string * t
  end =
  struct
    type t = int * string list

    let emp = 0, []
    let var i (_, xs) = List.nth xs i
    let bind (i, xs) =
      let x = "x" ^ string_of_int i in
      x, (i + 1, x :: xs)
  end

  let pp : type a. Env.t -> Format.formatter -> a t -> unit = 
    fun env fmt tm ->
      match out tm with
      | Var i -> 
        Format.fprintf fmt "%s" @@ 
        Env.var i env
      
      | _ ->
        Format.fprintf fmt "<term>"
end
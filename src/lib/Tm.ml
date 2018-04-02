type ('i, 'a) tube = 'i * 'i * 'a
type ('i, 'a) system = ('i, 'a) tube list

type atm = Thin.t0
type var = Thin.t0

type 'a vbnd = VB of 'a
type 'a abnd = AB of 'a

type chk = [`Chk]
type inf = [`Inf]

type info = Lexing.position * Lexing.position

type _ f =
  | Atom : atm -> inf f
  | Var : var -> inf f
  | Car : inf t -> inf f
  | Cdr : inf t -> inf f
  | App : inf t * chk t -> inf f
  | Down : {ty : chk t; tm : chk t} -> inf f
  | Coe : chk t * chk t * chk t abnd * chk t -> inf f
  | HCom : chk t * chk t * chk t * chk t * (chk t, chk t vbnd) system -> inf f

  | Up : inf t -> chk f

  | Univ : Lvl.t -> chk f
  | Pi : chk t * chk t vbnd -> chk f
  | Sg : chk t * chk t vbnd -> chk f
  | Ext : chk t * (chk t, chk t) system -> chk f
  | Interval : chk f

  | Lam : chk t vbnd -> chk f
  | Cons : chk t * chk t -> chk f
  | Dim0 : chk f
  | Dim1 : chk f

(* TODO: add explicit thinnings here *)
and 'a t = In of {info : info option; con : 'a f}

let into tf = In {info = None; con = tf}
let into_info info tf = In {info = Some info; con = tf}
let info (In node) = node.info

let out (In node) = node.con


let thin_var th t = failwith "todo"
let thin_atom th t = failwith "todo"

let path (VB ty, tm0, tm1) =
  let tube0 = (into @@ Up (into @@ Var Thin.id), into Dim0, thin_var (Thin.skip Thin.id) tm0) in
  let tube1 = (into @@ Up (into @@ Var Thin.id), into Dim1, thin_var (Thin.skip Thin.id) tm1) in
  into @@ Pi (into Interval, VB (into @@ Ext (ty, [tube0; tube1])))


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
    fun _ _ -> failwith "pp"
end
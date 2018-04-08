type name = string

type 'a f =
  | Atom of string
  | Numeral of int
  | List of 'a list
  | Bind of name * 'a

type info = Lexing.position * Lexing.position
type t = Node of {info : info; con : t f}

module type ResEnv =
sig
  type t
  val init : t
  val bind : string -> t -> t
  val get : string -> t -> Thin.t
end

module ResEnv : ResEnv = 
struct
  type t = string list

  let init = []
  let bind x env = x :: env
  let rec get x env =
    match env with 
    | [] ->
      failwith "variable not found"
    | y :: ys ->
      if x = y 
      then Thin.id
      else Thin.skip @@ get x ys
end

module Resolver (R : ResEnv) :
sig
  val chk : R.t -> t -> Tm.chk Tm.t
  val inf : R.t -> t -> Tm.inf Tm.t
end =
struct
  let rec chk env p =
    let Node pf = p in
    Tm.into_info pf.info @@
    match pf.con with
    | List [Node {con = Atom "lam"}; bdy] ->
      Tm.Lam (vbinder env bdy)
    | _ ->
      Tm.Up (inf env p)

  and vbinder env p =
    let Node pf = p in
    match pf.con with
    | Bind (x, p) ->
      Tm.B (chk (R.bind x env) p)
    | _ ->
      Tm.B (chk (R.bind "_" env) p)

  and inf (env : R.t) p =
    let Node pf = p in
    Tm.into_info pf.info @@
    match pf.con with
    | Atom x ->
      Tm.Var (R.get x env)
    | _ ->
      failwith "Reader could not understand parsetree"

end

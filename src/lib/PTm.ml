type name = string

type 'a f =
  | Atom of string
  | Numeral of int
  | List of 'a list
  | Bind of name * 'a

type 'a t = Node of {info : 'a; con : 'a t f}

module type ResEnv =
sig
  type t
  val bind : string -> t -> t
  val var : string -> t -> int
end

module Resolver (R : ResEnv) :
sig
  val chk : R.t -> 'a t -> Tm.chk
  val inf : R.t -> 'a t -> Tm.inf
end =
struct
  type 'a m = 'a

  let rec chk env p =
    let Node pf = p in
    match pf.con with
    | Atom "unit" -> Tm.Unit
    | Atom "bool" -> Tm.Bool
    | Atom "ax" -> Tm.Ax
    | Atom "tt" -> Tm.Tt
    | Atom "ff" -> Tm.Ff
    | Numeral 0 -> Tm.Dim0
    | Numeral 1 -> Tm.Dim1
    | List [Node {con = Atom "->"}; dom; cod] ->
      Tm.Pi (chk env dom, binder env cod)
    | List [Node {con = Atom "*"}; dom; cod] ->
      Tm.Sg (chk env dom, binder env cod)
    | List [Node {con = Atom "="}; cod; p0; p1] ->
      Tm.Eq (binder env cod, chk env p0, chk env p1)
    | List [Node {con = Atom "lam"}; bdy] ->
      Tm.Lam (binder env bdy)
    | List [Node {con = Atom "cons"}; hd; tl] ->
      Tm.Pair (chk env hd, chk env tl)
    | List [Node {con = Atom "U"}; Node {con = Numeral i}] ->
      Tm.U i
    | _ ->
      Tm.Up (inf env p)

  and binder env p =
    let Node pf = p in
    match pf.con with
    | Bind (x, p) ->
      Tm.B (chk (R.bind x env) p)
    | _ ->
      Tm.B (chk (R.bind "_" env) p)

  and inf env p =
    let Node pf = p in
    match pf.con with
    | Atom x ->
      Tm.Var (R.var x env)
    | List [Node {con = Atom "car"}; p] ->
      Tm.Proj1 (inf env p)
    | List [Node {con = Atom "cdr"}; p] ->
      Tm.Proj2 (inf env p)
    | List [Node {con = Atom "if"}; pmot; pb; pt; pf] ->
      Tm.If (binder env pmot, inf env pb, chk env pt, chk env pf)
    | List [Node {con = Atom ":"}; ptm; pty] ->
      Tm.Down (chk env pty, chk env ptm)
    | List [p1; p2] ->
      Tm.App (inf env p1, chk env p2)
    | _ -> failwith "resolver/inf"
end
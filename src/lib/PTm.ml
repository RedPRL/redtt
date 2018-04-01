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
  type 'a el = Var of 'a | Atom of 'a

  type t
  val init : t
  val bind : string el -> t -> t
  val var : string -> t -> int el
end

module ResEnv : ResEnv = 
struct
  type 'a el = Var of 'a | Atom of 'a

  (* TODO: variables and atoms *)
  type t = string el list

  let init = []

  let bind x env = x :: env

  let map f el = 
    match el with 
    | Var i -> Var (f i)
    | Atom i -> Atom (f i)

  let proj el = 
    match el with 
    | Var i -> i
    | Atom i -> i

  let rec var x (env : t) =
    match env with 
    | [] -> failwith "variable not found"
    | y :: ys -> if x = proj y then map (fun _ -> 0) y else map (fun i -> i + 1) @@ var x ys
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
      Tm.VB (chk (R.bind (R.Var x) env) p)
    | _ ->
      Tm.VB (chk (R.bind (R.Var "_") env) p)

  and inf (env : R.t) p =
    let Node pf = p in
    Tm.into_info pf.info @@
    match pf.con with
    | Atom x -> 
      begin
        match R.var x env with 
        | R.Atom i -> Tm.Atom i
        | R.Var i -> Tm.Var i
      end
    | _ -> failwith ""
end

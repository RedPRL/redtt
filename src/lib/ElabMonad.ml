module type StateMonad =
sig
  include Monad.S

  type state
  val get : state m
  val set : state -> unit m
end

module State (T : sig type t end) : StateMonad with type state = T.t = 
struct
  type state = T.t
  type 'a m = state -> state * 'a
  let ret a st = st, a
  let bind m k st = let st', a = m st in k a st'
  let get st = st, st
  let set st _ = st, ()
end

type tm = Tm.chk Tm.t 
type ty = Tm.chk Tm.t 
type rtm = ResEnv.t -> tm

type hyp = string option * ty
type subgoal = hyp list * ty
type meta = Symbol.t

module Cfg =
struct
  type t =
    {mcx : MCx.t;
     zip : meta Tree.zip}
end

module M = State (Cfg)
include M

module MonadNotation = Monad.Notation(M)
open MonadNotation

let sequent : MCx.sequent m = 
  get >>= fun cfg ->
  let x = Tree.cursor cfg.zip in
  ret @@ MCx.lookup_exn x cfg.mcx


let eval tm : Val.can Val.t m = 
  get >>= fun cfg ->
  let x = Tree.cursor cfg.zip in
  let seq = MCx.lookup_exn x cfg.mcx in
  let menv = MCx.menv cfg.mcx in 
  ret @@ Val.eval (menv, LCx.env seq.lcx) seq.ty


let quote_ty v : tm m =
  get >>= fun cfg ->
  let x = Tree.cursor cfg.zip in
  let seq = MCx.lookup_exn x cfg.mcx in
  let univ = Val.into @@ Val.Univ Lvl.Omega in
  ret @@ Quote.quote (LCx.len seq.lcx) ~ty:univ v


let goal : ty m = 
  sequent >>= fun seq ->
  eval seq.ty >>= quote_ty

let subgoal ~hyps ~ty = 
  hyps, ty

let oblige : subgoal -> meta m = 
  fun (hyps, ty) ->
    get >>= fun cfg ->
    sequent >>= fun seq ->

    let univ = Val.into @@ Val.Univ Lvl.Omega in

    let rnv, lcx = 
      let alg (nm, ty) (rnv, lcx) =
        Typing.check ~mcx:cfg.mcx ~cx:lcx ~ty:univ ~tm:ty;
        let vty = Val.eval (MCx.menv cfg.mcx, LCx.env lcx) ty in
        ResEnv.bind_opt nm rnv, LCx.ext lcx ~nm vty
      in List.fold_right alg hyps (seq.rnv, seq.lcx)
    in

    Typing.check ~mcx:cfg.mcx ~cx:lcx ~ty:univ ~tm:ty;

    let seq' = MCx.{rnv; lcx; ty; cell = MCx.Ask} in
    let y = Symbol.fresh () in
    let mcx = MCx.ext y seq' cfg.mcx in
    let zip = Tree.insert y cfg.zip in
    set {mcx; zip} >>
    ret y

let fill : tm -> unit m = 
  fun tm ->
    get >>= fun cfg ->
    let x = Tree.cursor cfg.zip in
    let seq = MCx.lookup_exn x cfg.mcx in
    match seq.cell with
    | Ask -> 
      let vty = Val.eval (MCx.menv cfg.mcx, LCx.env seq.lcx) seq.ty in
      Typing.check ~mcx:cfg.mcx ~cx:seq.lcx ~ty:vty ~tm;
      set @@ {cfg with mcx = MCx.set x tm cfg.mcx}

    | Ret _ ->
      failwith "Cannot fill resolved hole"

let resolve : rtm -> tm m = 
  fun rtm -> 
    sequent >>= fun seq ->
    ret @@ rtm seq.rnv

let move : Tree.move -> unit m =
  fun mv ->
    get >>= fun cfg ->
    set @@ {cfg with zip = Tree.move mv cfg.zip}

let move0 m = 
  move (`Id m)

module Notation = 
struct
  let (>-) hyps ty = subgoal ~hyps ~ty
end
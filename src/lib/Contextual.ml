open Dev
open RedBasis
open Bwd open BwdNotation

module Subst = GlobalCx

type cx_l = entry bwd
type cx_r = [`Entry of entry | `Subst of Subst.t] list

type cx = cx_l * cx_r

module M =
struct
  type 'a m = params -> cx -> cx * 'a

  let ret a _ cx = cx, a

  let bind m k ps cx =
    let cx', a = m ps cx  in
    k a ps cx'
end

module Notation = Monad.Notation (M)
include M

open Notation

let local f m ps =
  m (f ps)

let optional m ps cx =
  try
    let cx', a = m ps cx in
    cx', Some a
  with
  | _ -> cx, None

let ask ps cx = cx, ps

let get _ cx = cx, cx

let modify f _ cx = f cx, ()

let getl = fst <@> get
let getr = snd <@> get
let modifyl f = modify @@ fun (l, r) -> f l, r
let modifyr f = modify @@ fun (l, r) -> l, f r
let setl l = modifyl @@ fun _ -> l
let setr r = modifyr @@ fun _ -> r
let pushl e = modifyl @@ fun es -> es #< e
let pushr e = modifyr @@ fun es -> `Entry e :: es

let rec pushls es =
  match es with
  | [] -> ret ()
  | e :: es ->
    pushl e >>
    pushls es

let popl =
  getl >>= function
  | Snoc (mcx, e) -> setl mcx >> ret e
  | _ -> failwith "popl: empty"


let subst_tm sub ~ty tm =
  let module T = Typing.M (struct let globals = sub end) in
  let vty = T.Cx.eval T.Cx.emp ty in
  let el = T.Cx.eval T.Cx.emp tm in
  T.Cx.quote T.Cx.emp ~ty:vty el

let subst_decl sub ~ty =
  function
  | Hole ->
    Hole
  | Defn t ->
    Defn (subst_tm sub ~ty t)

let subst_equation sub q =
  let univ = Tm.univ ~kind:Kind.Pre ~lvl:Lvl.Omega in
  let ty0 = subst_tm sub ~ty:univ q.ty0 in
  let ty1 = subst_tm sub ~ty:univ q.ty1 in
  let tm0 = subst_tm sub ~ty:ty0 q.tm0 in
  let tm1 = subst_tm sub ~ty:ty1 q.tm1 in
  {ty0; ty1; tm0; tm1}

let subst_param sub =
  let univ = Tm.univ ~kind:Kind.Pre ~lvl:Lvl.Omega in
  function
  | P ty ->
    P (subst_tm sub ~ty:univ ty)
  | Tw (ty0, ty1) ->
    Tw (subst_tm sub ~ty:univ ty0, subst_tm sub ~ty:univ ty1)

let rec subst_problem sub =
  function
  | Unify q ->
    Unify (subst_equation sub q)
  | All (param, prob) ->
    let param' = subst_param sub param in
    let x, probx = unbind prob in
    let probx' = subst_problem sub probx in
    let prob' = Dev.bind x probx' in
    All (param', prob')


let subst_entry sub =
  function
  | E (x, ty, decl) ->
    let univ = Tm.univ ~kind:Kind.Pre ~lvl:Lvl.Omega in
    E (x, subst_tm sub ~ty:univ ty, subst_decl sub ~ty decl)
  | Q (s, p) ->
    let p' = subst_problem sub p in
    let s' = if p = p' then s else Active in
    Q (s', p')

let popr =
  let rec go sub =
    getr >>= function
    | `Entry e :: mcx ->
      let e' = subst_entry sub e in
      setr (`Subst sub :: mcx) >>
      ret e'
    | `Subst sub' :: mcx ->
      setr mcx >>
      go @@ Subst.merge sub sub'
    | [] ->
      failwith "popr: empty"
  in
  go Subst.emp

let go_left =
  popl >>= fun e ->
  pushr e


let in_scope x p =
  local @@ fun ps ->
  ps #< (x, p)


let lookup_var x w =
  let rec go gm =
    match w, gm with
    | `Only, Snoc (gm, (y, P ty)) ->
      if x = y then M.ret ty else go gm
    | `TwinL, Snoc (gm, (y, Tw (ty0, _))) ->
      if x = y then M.ret ty0 else go gm
    | `TwinR, Snoc (gm, (y, Tw (_, ty1))) ->
      if x = y then M.ret ty1 else go gm
    | _, Snoc (gm, _) ->
      go gm
    | _ ->
      failwith "lookup_var: not found"
  in
  ask >>= go

let lookup_meta x =
  let rec look =
    function
    | Snoc (mcx, E (y, ty, _)) ->
      if x = y then M.ret ty else look mcx
    | Snoc (mcx, _) ->
      look mcx
    | Emp ->
      failwith "lookup_meta: not found"
  in
  getl >>= look


let unleash_subst x tm =
  lookup_meta x >>= fun ty ->
  modifyr @@ fun es ->
  let sub = Subst.define Subst.emp x ~ty ~tm in
  `Subst sub :: es

let postpone s p =
  ask >>= fun ps ->
  let wrapped =
    let rec go ps p =
      match ps with
      | Snoc (ps, (x, e)) ->
        go ps @@ All (e, Dev.bind x p)
      | Emp -> p
    in go ps p
  in
  pushr @@ Q (s, wrapped)


let active = postpone Active
let block = postpone Blocked


let cx_core : cx_l -> GlobalCx.t =
  let rec go es =
    match es with
    | Emp -> GlobalCx.emp
    | Snoc (es, e) ->
      match e with
      | E (x, ty, Hole) ->
        let cx = go es in
        GlobalCx.add_hole cx x ty []
      | E (x, ty, Defn t) ->
        let cx = go es in
        GlobalCx.define cx x ty t
      | Q _ ->
        go es
  in
  go


let typechecker : (module Typing.S) m =
  getl >>= fun entries ->
  let globals = cx_core entries in
  let module G = struct let globals = globals end in
  let module T = Typing.M (G) in
  ret @@ (module T : Typing.S)

let check ~ty tm =
  typechecker >>= fun (module T) ->
  let lcx = T.Cx.emp in
  let vty = T.Cx.eval lcx ty in
  try
    T.check lcx vty tm;
    ret true
  with
  | _ ->
    ret false

let check_eq ~ty tm0 tm1 =
  typechecker >>= fun (module T) ->
  let lcx = T.Cx.emp in
  let vty = T.Cx.eval lcx ty in
  let el0 = T.Cx.eval lcx tm0 in
  let el1 = T.Cx.eval lcx tm1 in
  try
    T.Cx.check_eq lcx ~ty:vty el0 el1;
    ret true
  with
  | _ ->
    ret false

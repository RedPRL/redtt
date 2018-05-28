open RedBasis.Bwd

type tm = Tm.tm
type ty = Tm.tm

type twin = [`Only | `TwinL | `TwinR]

type 'a decl =
  | Hole
  | Defn of 'a

type status =
  | Blocked
  | Active

type ('a, 'b) equation =
  {ty0 : ty;
   tm0 : 'a;
   ty1 : ty;
   tm1 : 'b}

type param =
  | P of ty
  | Tw of ty * ty

type params = (Name.t * param) bwd

type 'a bind = B of 'a

type problem =
  | Unify of (tm, tm) equation
  | All of param * problem bind

type entry =
  | E of Name.t * ty * tm decl
  | Q of status * problem

let bind _ _ = failwith ""

let unbind (B _prob) =
  let _x = Name.fresh () in
  failwith ""

module Subst = GlobalCx

module type DevSort =
sig
  include Occurs.S
  val subst : Subst.t -> t -> t
end

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
    let prob' = bind x probx' in
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


module Param =
struct
  type t = param
  let free fl =
    function
    | P ty -> Tm.free fl ty
    | Tw (ty0, ty1) ->
      Occurs.Set.union (Tm.free fl ty0) (Tm.free fl ty1)

  let subst = subst_param
end

module Params = Occurs.Bwd (Param)

module Decl =
struct
  type t = Tm.tm decl
  let free fl =
    function
    | Hole -> Occurs.Set.empty
    | Defn t -> Tm.free fl t

  let subst = subst_decl
end


module Equation =
struct
  type t = (tm, tm) equation
  let free fl {ty0; tm0; ty1; tm1} =
    let sets =
      [ Tm.free fl ty0;
        Tm.free fl tm0;
        Tm.free fl ty1;
        Tm.free fl tm1 ]
    in List.fold_right Occurs.Set.union sets Occurs.Set.empty

  let sym q =
    {ty0 = q.ty1; tm0 = q.tm1; ty1 = q.ty0; tm1 = q.tm0}

  let subst = subst_equation
end

module Problem =
struct
  type t = problem
  let rec free fl =
    function
    | Unify q ->
      Equation.free fl q
    | All (p, B prob) ->
      Occurs.Set.union (Param.free fl p) (free fl prob)

  let eqn ~ty0 ~tm0 ~ty1 ~tm1 =
    Unify {ty0; tm0; ty1; tm1}

  let all x ty prob =
    All (P ty, bind x prob)

  let all_twins x ty0 ty1 prob =
    All (Tw (ty0, ty1), bind x prob)

  let subst = subst_problem
end

module Entry =
struct
  type t = entry
  let free fl =
    function
    | E (_, _, d) ->
      Decl.free fl d
    | Q (_, p) ->
      Problem.free fl p

  let subst = subst_entry
end

module Entries : Occurs.S with type t = entry list =
  Occurs.List (Entry)

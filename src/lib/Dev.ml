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


module Param =
struct
  type t = param
  let free fl =
    function
    | P ty -> Tm.free fl ty
    | Tw (ty0, ty1) ->
      Occurs.Set.union (Tm.free fl ty0) (Tm.free fl ty1)
end

module Params = Occurs.Bwd (Param)

module Decl =
struct
  type t = Tm.tm decl
  let free fl =
    function
    | Hole -> Occurs.Set.empty
    | Defn t -> Tm.free fl t
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
end

module Entries : Occurs.S with type t = entry list =
  Occurs.List (Entry)

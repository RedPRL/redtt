
type tm = Tm.tm
type ty = Tm.tm

type twin = [`Only | `TwinL | `TwinR]

type 'a decl =
  | Hole
  | Defn of 'a

type status =
  | Blocked
  | Active

type equation =
  {ty0 : ty; tm0 : tm; ty1 : ty; tm1 : ty}

type param =
  | P of ty
  | Tw of ty * ty

type params = (Name.t * param) list

type 'a bind = B of 'a

type problem =
  | Unify of equation
  | All of param * problem bind

type entry =
  | E of Name.t * ty * tm decl
  | Q of status * problem

let bind _ _ = failwith ""

let unbind (B _prob) =
  let _x = Name.fresh () in
  failwith ""


module Prob =
struct
  let eqn ty0 tm0 ty1 tm1 =
    Unify {ty0; tm0; ty1; tm1}

  let all x ty prob =
    All (P ty, bind x prob)

  let all_twins x ty0 ty1 prob =
    All (Tw (ty0, ty1), bind x prob)
end

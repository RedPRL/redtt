
type tm = Tm.tm
type ty = Tm.tm

type 'a decl =
  | Hole
  | Defn of 'a

type status =
  | Blocked
  | Active

type equation =
  | Eqn of {ty0 : ty; tm0 : tm; ty1 : ty; tm1 : ty}

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

let unbind (B prob) =
  let _x = Name.fresh () in
  failwith ""


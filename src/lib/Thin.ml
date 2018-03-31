type ('x, 'a) f = 
  | Id
  | Keep of 'a
  | Skip of 'a
  | Sub of 'a * 'x

type 'x t = In of ('x, 'x t) f
type t0 = Void.t t

let out (In th) = th

let id = In Id
let keep t = In (Keep t)
let skip t = In (Skip t)
let sub t a = In (Sub (t, a))

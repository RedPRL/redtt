(* TODO: this will become the source language,
   which gets elaborated into the core calculus. *)


type chk = Tm.chk
type inf = Tm.inf

type _ f =
  | Pi : tele -> chk f
  | Sg : tele -> chk f
  | Lam : {vars : string list; bdy : chk t} -> chk f
  | Tuple : {cells : chk t list} -> chk f
  | Hole : chk f
  | Quote : (ResEnv.t -> chk Tm.t) -> chk f

and tele =
  | TCons of {vars : string list; dom : chk t; cod : tele}
  | TEnd of {cod : chk t}

and 'a t = {con : 'a f}

let out : type a. a t -> a f =
  fun t ->
    t.con

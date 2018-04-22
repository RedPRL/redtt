(* TODO: this will become the source language,
   which gets elaborated into the core calculus. *)


type chk = Tm.chk
type inf = Tm.inf

type _ f =
  | Pi : tele -> chk f
  | Sg : tele -> chk f
  | Lam : {vars : string list} -> chk f
  | Tuple : {cells : chk t list} -> chk f
  | Hole : chk f
  | Quote : {tm : ResEnv.t -> 'a Tm.t} -> 'a f

and tele = 
  | TCons of {vars : string list; dom : chk t; cod : tele}
  | TEnd of {cod : chk t}

and 'a t = {con : 'a t f}
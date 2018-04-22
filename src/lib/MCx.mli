(* metacontext *)

type t
type meta = Symbol.t


(* In case someone asks, why are the terms and types stored as terms rather than values:

   These terms are used in many different contexts (under explicit substitutions), 
   and it doesn't make sense to substitute in *value*. But we do know how to
   take a term and evaluate it under an explicit substitution. *)

type cell = 
  | Ret of Tm.chk Tm.t
  | Ask

type sequent = {lcx : LCx.t; rnv : ResEnv.t; ty : Tm.chk Tm.t; cell : cell}

val emp : t
val ext : meta -> sequent -> t -> t
val set : meta -> Tm.chk Tm.t -> t -> t

val lookup_exn : meta -> t -> sequent
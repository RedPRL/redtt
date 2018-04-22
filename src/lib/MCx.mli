(* metacontext *)

type t
type meta = Symbol.t

type cell = 
  | Ret of Tm.chk Tm.t
  | Ask

type sequent = {lcx : LCx.t; ty : Tm.chk Tm.t; cell : cell}

val emp : t
val ext : meta -> sequent -> t -> t
val set : meta -> Tm.chk Tm.t -> t -> t

val lookup_exn : meta -> t -> sequent
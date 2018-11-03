type atom = I.atom
type dim = I.t

type t

type 'a m = [`Changed of 'a | `Same | `Inconsistent]

(* core API *)
val emp : unit -> t
val equate : dim -> dim -> t -> t m (* may raise I.Inconsistent *)
val hide : atom -> t -> t m
val subst : dim -> atom -> t -> t m
val swap : atom -> atom -> t -> t (* this is not using `t m` *)
val compare : dim -> dim -> t -> I.compare

(* convenience functions *)
val equate' : dim -> dim -> t -> t
val hide' : atom -> t -> t
val subst' : dim -> atom -> t -> t

(* pretty printer *)
val pp : Format.formatter -> t -> unit


(* to be deleted *)
val from_old_restriction : Restriction.t -> t

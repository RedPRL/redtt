(** Development contexts. Following Conor McBride, we define tactics to be admissible rules
    in the theory of valid contexts. *)

type t
val emp : t
val ext : t -> Dev.cell -> t

val pp_cx : t Pretty.t0
val ppenv : t -> Pretty.env

(** Compile a development context to a core-language context, for type checking.
    Guess binders turn into variable bindings (the guessed term is invisible), just like
    lambda binders. Let binders turn into definitions (which can be seen in type checking).
    Restrictions get turned into restrictions. *)
val core : GlobalCx.t -> t -> Typing.cx


(** Given a type [cod], render the context into a big pi type ending in [cod]; return this type
    together with a list of arguments that a hole can be applied to. *)
val skolemize : t -> cod:Tm.chk Tm.t -> Tm.chk Tm.t * Tm.chk Tm.t list


exception EmptyContext
val pop : t -> t

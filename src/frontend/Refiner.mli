open RedTT_Core
open Dev
open ElabMonad

type chk_tac = ty -> tm m

exception ChkMatch

(** Try to run a tactic against the current type, but if it raises ChkMatch, re-run it after normalizing the type. *)
val tac_wrap_nf : chk_tac -> chk_tac


(** Multi-introduction tactic *)
val tac_lambda : string list -> chk_tac -> chk_tac


(** A tactical which adds support for restriction *)
val tac_rst : chk_tac -> chk_tac

val normalize_ty : ty -> ty m


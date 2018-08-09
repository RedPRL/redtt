open Dev
open RedTT_Core
open ElabMonad

type chk_tac = ty -> tm m
type inf_tac = (ty * tm) m

exception ChkMatch

(** Try to run a tactic against the current type, but if it raises [ChkMatch], re-run it after normalizing the type. *)
val tac_wrap_nf : chk_tac -> chk_tac


(** Multi-introduction tactic *)
val tac_lambda : string list -> chk_tac -> chk_tac

val tac_elim : tac_mot:chk_tac option -> tac_scrut:inf_tac -> clauses:(Desc.con_label * ESig.epatbind list * chk_tac) list -> chk_tac

val tac_let : string -> inf_tac -> chk_tac -> chk_tac


(** A tactical which adds support for restriction *)
val tac_rst : chk_tac -> chk_tac

val normalize_ty : ty -> ty m


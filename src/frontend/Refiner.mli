open Dev
open RedTT_Core
open ElabMonad

type sys = (tm, tm) Tm.system
type goal = {ty : ty; sys : sys}
type chk_tac = goal -> tm m
type inf_tac = (ty * tm) m

exception ChkMatch

val auto : chk_tac
val hope : chk_tac

(** Try to run a tactic against the current type, but if it raises [ChkMatch], re-run it after normalizing the type. *)
val tac_wrap_nf : chk_tac -> chk_tac


(** Multi-introduction tactic *)
val tac_lambda : string list -> chk_tac -> chk_tac

val tac_elim : loc:location -> tac_mot:chk_tac option -> tac_scrut:inf_tac -> clauses:(Desc.con_label * ESig.epatbind list * chk_tac) list -> chk_tac

val tac_let : string -> inf_tac -> chk_tac -> chk_tac


val guess_restricted : tm -> chk_tac

val normalize_ty : ty -> ty m



val bind_in_scope : tm -> tm m

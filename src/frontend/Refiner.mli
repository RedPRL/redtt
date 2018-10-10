open Dev
open RedTT_Core
open Contextual

type sys = (tm, tm) Tm.system
type goal = {ty : ty; sys : sys}
type chk_tac = goal -> tm m
type inf_tac = (ty * tm) m

exception ChkMatch

(** Decompose the current goal and try to solve it by reflexivity automatically. *)
val tac_refl : chk_tac

(** Try to solve the current goal using the current restriction, and/or unification. *)
val tac_hope : chk_tac


val inspect_goal : loc:Log.location -> name:string option -> goal -> unit m

(** Unleash a hole named [name]. *)
val tac_hole : loc:Log.location -> name:string option -> chk_tac

(** Run the input tactic without the restriction, and then store the result
    as a guess for the current hole in the proof state. *)
val tac_guess : chk_tac -> chk_tac


val tac_fix : (chk_tac -> chk_tac) -> chk_tac
val match_goal : (goal -> chk_tac) -> chk_tac


(** Try to run a tactic against the current type, but if it raises [ChkMatch], re-run it after normalizing the type. *)
val tac_wrap_nf : chk_tac -> chk_tac

(** Multi-introduction tactic *)
val tac_lambda : ML.einvpat list -> chk_tac -> chk_tac

(** Introduce a sigma type *)
val tac_pair : chk_tac -> chk_tac -> chk_tac

(** Call a data elimination rule. *)
val tac_elim
  : loc:Log.location
  -> tac_mot:chk_tac option
  -> tac_scrut:inf_tac
  -> clauses:(string * ML.einvpat ML.epatbind list * chk_tac) list
  -> default:chk_tac option
  -> chk_tac

(** Call a data elimination rule. *)
val tac_elim_inf
  : loc:Log.location
  -> tac_mot:chk_tac
  -> tac_scrut:inf_tac
  -> clauses:(string * ML.einvpat ML.epatbind list * chk_tac) list
  -> default:chk_tac option
  -> inf_tac

val tac_generalize
  : tac_scrut:inf_tac
  -> chk_tac
  -> chk_tac

(** Introduce a let-binding. *)
val tac_let : Name.t -> inf_tac -> chk_tac -> chk_tac
val tac_inv_let : ML.einvpat -> inf_tac -> chk_tac -> chk_tac

(** Try to solve a goal with a term, unifying it against the ambient restriction. *)
val guess_restricted : tm -> chk_tac


val normalize_ty : ty -> ty m
val bind_sys_in_scope : (tm, tm) Tm.system -> (tm, tm) Tm.system m
val bind_in_scope : tm -> tm m

val name_of : [`User of string | `Gen of Name.t] -> Name.t


val unify : unit m

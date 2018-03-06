open Tm
open Val

val apply : d -> d -> d

val eval : env -> chk -> d
val eval_inf : env -> inf -> d
val eval_sub : env -> sub -> env
(* val eval_ctx : ctx -> env *)

val quo_nf : Ctx.t -> dnf -> chk

(* val nbe : ctx -> tm:chk -> ty:chk -> chk *)
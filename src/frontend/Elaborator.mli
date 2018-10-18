module type Import =
sig
  val import : per_process : Contextual.per_process -> mlconf : ML.mlconf -> selector : FileRes.selector
    -> [`New of ResEnv.t * Contextual.per_process | `Cached of ResEnv.t]
end

module type S =
sig
  val eval_cmd : ML.mlcmd -> ML.semcmd Contextual.m 
end

module Make (I : Import) : S

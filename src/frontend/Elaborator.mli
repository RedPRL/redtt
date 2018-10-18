module type Import =
sig
  val import : persistent_env : Contextual.persistent_env -> mlconf : ML.mlconf -> selector : FileRes.selector
    -> [`New of Contextual.persistent_env * ResEnv.t | `Cached of ResEnv.t]
end

module type S =
sig
  val eval_cmd : ML.mlcmd -> ML.semcmd Contextual.m 
end

module Make (I : Import) : S

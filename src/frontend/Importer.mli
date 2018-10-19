module M :
sig
  val load_file
    : persistent_env_opt : Contextual.persistent_env option
    -> mlconf : ML.mlconf
    -> string
    -> [`New of Contextual.persistent_env * ResEnv.t | `Cached of ResEnv.t]

  val load_stdin
    : persistent_env_opt : Contextual.persistent_env option
    -> mlconf : ML.mlconf
    -> stem : string
    -> Contextual.persistent_env * ResEnv.t

  val import
    : persistent_env : Contextual.persistent_env
    -> mlconf : ML.mlconf
    -> selector : FileRes.selector
    -> [`New of Contextual.persistent_env * ResEnv.t | `Cached of ResEnv.t]
end

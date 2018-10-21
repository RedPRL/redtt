module type Import =
sig
  val top_load_file : FileRes.filepath -> unit Contextual.m
  val top_load_stdin : red : FileRes.filepath -> unit Contextual.m
  val import : selector : FileRes.selector -> ResEnv.t Contextual.m
end

module type S =
sig
  val eval_cmd : ML.mlcmd -> ML.semcmd Contextual.m 
end

module Make (I : Import) : S

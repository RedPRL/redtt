module type Import =
sig
  val include_file : FileRes.filepath -> unit Contextual.m
  val include_stdin : filename : FileRes.filepath -> unit Contextual.m
  val import : selector : FileRes.selector -> ResEnv.t Contextual.m
end

module type S =
sig
  val eval_cmd : ML.mlcmd -> ML.semcmd Contextual.m 
end

module Make (I : Import) : S

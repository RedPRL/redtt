open Contextual

module M :
sig
  (** load the content of file at the top module. *)
  val top_load_file : FileRes.filepath -> unit m

  (** load from the standard input at the top module. *)
  val top_load_stdin : red : FileRes.filepath -> unit m

  (** import some module. *)
  val import : selector : FileRes.selector -> ResEnv.t m
end

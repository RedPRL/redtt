open Contextual

module M :
sig
  (** include a file as if its content is copy-pasted into the current module,
      followed by a report on unresolved meta variables. *)
  val include_file : FileRes.filepath -> unit m

  (** include the content from the standard input as if it is copy-pasted
      into the current module, followed by a report on unresolved meta variables. *)
  val include_stdin : filename : FileRes.filepath -> unit m

  (** import some module. *)
  val import : selector : FileRes.selector -> ResEnv.t m
end

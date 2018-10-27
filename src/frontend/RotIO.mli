open Contextual

val set_unsafe_mode : bool -> unit

val try_read :
  redsum : Digest.t option -> (* if you already know the redsum *)
  importer : (selector : FileRes.selector -> rotted_resolver Contextual.m) ->
  stem : FileRes.filepath ->
  rotted_resolver option m

(* this writes the rot file and returns the checksum of
   the supposed rot file. *)
val write : rotted_resolver m

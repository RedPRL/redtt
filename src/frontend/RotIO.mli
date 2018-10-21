open Contextual

val set_unsafe_mode : bool -> unit

(* val read : rot m *)

(* this writes the rot file and returns the checksum of
   the supposed rot file. *)
val write : rotted_resolver m

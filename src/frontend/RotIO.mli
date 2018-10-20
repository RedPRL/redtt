open RotData
open Contextual

val set_unsafe_mode : bool -> unit
val read_rot_file : FileRes.selector -> rot m
val write_rot_file : FileRes.selector -> rot -> unit m

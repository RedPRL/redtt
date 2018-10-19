open RotData
open Contextual

val read_rot_file : FileRes.selector -> rot m
val write_rot_file : FileRes.selector -> rot -> unit m

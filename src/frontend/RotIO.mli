open RedBasis
open RedTT_Core
open RotData

type cache = (string, ResEnv.t) Hashtbl.t
include Monad.S
val read_rot_file : FileRes.selector -> rot m
val write_rot_file : FileRes.selector -> rot -> unit m
val run : cache -> GlobalEnv.t -> ResEnv.t -> 'a m -> GlobalEnv.t * 'a

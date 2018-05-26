open RedBasis
open Dev

include Monad.S

val popl : entry m
val popr : entry m
val pushl : entry -> unit m
val pushr : entry -> unit m
val pushls : entry list -> unit m
val go_left : unit m

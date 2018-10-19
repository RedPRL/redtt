exception Not_found

type selector = string list

val selector_to_stem : base_dir : string -> selector -> string
val selector_to_red : base_dir : string -> selector -> string
val selector_to_rot : base_dir : string -> selector -> string
val red_to_stem : string -> string

exception Not_found

type filepath = string
type dirpath = string
type selector = string list

val selector_to_stem : base_dir : dirpath -> selector -> filepath
val selector_to_red : base_dir : dirpath -> selector -> filepath
val selector_to_rot : base_dir : dirpath -> selector -> filepath
val red_to_stem : filepath -> filepath
val stem_to_red : filepath -> filepath
val stem_to_rot : filepath -> filepath

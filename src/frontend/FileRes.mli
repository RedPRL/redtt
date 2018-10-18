exception Not_found

type local_selector = string list
type selector = local_selector list

(** might raise [Not_found] *)
val module_to_path : base_dir : string -> ?extension : string option -> local_selector -> string

val normalize_selector : base_dir : string -> selector -> selector

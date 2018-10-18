exception Not_found

type selector = string list

(** might raise [Not_found] *)
val module_to_path : base_dir : string -> ?extension : string option -> selector -> string

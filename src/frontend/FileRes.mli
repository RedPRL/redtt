type selector = string list

(** might raise [Not_found] *)
val find_module : string -> ?extension : string option -> selector -> string

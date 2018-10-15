(** portable and reasonable normalization of a mix of absolute and relative paths
    into an absolute path based on chdir/getcwd. *)
val normalize_concat : dirs : string list -> rel_path : string -> string

(** run a {b gyve} and then restore the current cwd. *)
val protect_cwd : (string -> 'a) -> 'a

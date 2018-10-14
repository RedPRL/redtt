module SysUtil :
sig
  (** turn [["a"; "b"; "c"]] into ["a/b/c"]. note that [extension]
      should {b not} include the period. *)
  val module_to_rel_path : ?extension:string -> string list -> string

  (** portable and reasonable normalization of a mix of absolute and relative paths
      into an absolute path based on chdir/getcwd. *)
  val normalize_concat : dirs:string list -> rel_path:string -> string

  (** run a {b gyve} and then restore the current cwd. *)
  val protect_cwd : (string -> 'a) -> 'a
end =
struct
  let module_to_rel_path ?extension accessors =
    let without_ext = String.concat Filename.dir_sep accessors in
    match extension with
    | None -> without_ext
    | Some ext -> String.concat "." [without_ext; ext]

  let protect_cwd f =
    let dir = Sys.getcwd () in
    let ans = f dir in
    Sys.chdir dir;
    ans

  let normalize_concat ~dirs ~rel_path =
    protect_cwd @@ fun _ ->
    List.iter Sys.chdir dirs;
    Sys.chdir (Filename.dirname rel_path);
    Filename.concat (Sys.getcwd ()) (Filename.basename rel_path)

  let () : unit =
    if Filename.is_relative (Sys.getcwd ()) then
      failwith "Sys.getcwd returns a relative path."
    else
      ()
end

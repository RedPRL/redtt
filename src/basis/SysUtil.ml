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

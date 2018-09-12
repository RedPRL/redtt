type options =
  {file_name : Lwt_io.file_name;
   line_width: int}

val load_file : options -> unit Lwt.t
val load_from_stdin : options -> unit Lwt.t

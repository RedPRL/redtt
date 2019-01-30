type options =
  {file_name : string;
   line_width : int;
   debug_mode : bool;
   shell_mode : bool;
   recheck : bool}

val load_file : options -> unit
val load_from_stdin : options -> unit

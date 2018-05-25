type t =
  | Define of {name : string; info : Tm.info; args : TmUtil.tele; body : Tm.tm}

type document = t list

val check_document : document -> unit

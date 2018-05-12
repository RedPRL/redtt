type t =
  | Define of {name : string; info : Tm.info; args : TmUtil.tele; body : Tm.chk Tm.t}

type document = t list

val check_document : Typing.Cx.t -> document -> unit

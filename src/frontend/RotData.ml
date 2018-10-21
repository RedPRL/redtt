open RedTT_Core

let version : string = "Where do correct ideas come from?"

type dep =
  | True
  | False
  | Libsum (* always true, for now *)
  | Self of {stem : FileRes.filepath; redsum : Digest.t}
  | Import of {sel : FileRes.selector; stem : FileRes.filepath; rotsum : Digest.t}
  | Shell of {cmd : string; exit: int}

type datum =
  | P of {ty : Tm.tm}
  | Def of {ty : Tm.tm; tm : Tm.tm}
  | Desc of Desc.desc

type repo = (string option * datum) list

(* this is not really used, but is useful as an overview

type rot =
  Rot of
    {ver : string;
     deps : dep list;
     res : rot_resource}
*)

open RedTT_Core

let version : string = "Where do correct ideas come from?"

type dep =
  | True
  | False
  | SelfAt of {stem : FileRes.filepath}
  | Redsum of {hash : Digest.t}
  | Libsum of {hash : Digest.t}
  | Rotsum of {stem : FileRes.filepath; hash : Digest.t}
  | Shell of {cmd : string; exit: int}

type datum =
  | P of {ty : Tm.tm}
  | Def of {ty : Tm.tm; tm : Tm.tm}
  | Desc of Desc.desc

type rot_resource = (string option * datum) list

type rot =
  Rot of
    {ver : string;
     deps : dep list;
     res : rot_resource}

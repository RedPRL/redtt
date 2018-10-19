open RedTT_Core

let version : string = "Where do correct ideas come from?"

type dep =
  | True
  | False
  | Redsum of {hash : Digest.t}
  | Rotsum of {sel : FileRes.selector; hash : Digest.t}
  | Shell of {cmd : string}

type datum =
  | Down of {ty : Tm.tm; tm : Tm.tm}
  | Desc of Desc.desc

type entry =
  {name : string;
   visibility : ResEnv.visibility;
   id : int}

type rot =
  {deps : dep list;
   imports : FileRes.filepath list;
   data : datum list;
   resolver : entry list}

open RedTT_Core

let version : string = "Where do correct ideas come from?"

type selector = FileRes.selector
type visibility = ResEnv.visibility

type dep =
  | True
  | False
  | Redsum of {hash : Digest.t}
  | Rotsum of {sel : selector; hash : Digest.t}
  | Shell of {cmd : string}

type datum =
  | Down of {ty : Tm.tm; tm : Tm.tm}
  | Desc of Desc.desc

type entry =
  {name : string;
   visibility : visibility;
   id : int}

type rot =
  {deps : dep list;
   imports : selector list;
   data : datum list;
   resolver : entry list}

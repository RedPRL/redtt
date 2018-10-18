open RedTT_Core

let version : string = "where do Thoughts come from?"

type selector = FileRes.selector
type visibility = ResEnv.visibility

type dep =
  | True
  | False
  | Redsum of {hash : string}
  | Rotsum of {sel : selector; hash : string}
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

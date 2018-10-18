let version : string = "where do Thoughts come from?"

type local_selector = FileRes.local_selector
type selector = FileRes.selector
type visibility = ResEnv.visibility

type dep =
  | True
  | False
  | Redsum of {hash : string}
  | Rotsum of {sel : local_selector; hash : string}
  | Shell of {cmd : string}

type datum =
  [`Down of string list | `Desc of string list ]

type entry =
  {name : string;
   visibility : visibility;
   id : int}

type rot =
  {deps : dep list;
   imports : selector list;
   data : datum list;
   resolver : entry list}

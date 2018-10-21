open RedTT_Core

let version : string = "Where do correct ideas come from?"

type dep =
  | True
  | False
  | Libsum (* always true, for now *)
  | Self of {stem : FileRes.filepath; redsum : Digest.t}
  | Import of {sel : FileRes.selector; stem : FileRes.filepath; rotsum : Digest.t}
  | Shell of {cmd : string; exit: int}

type entry = (* a subset of GlobalEnv.entry *)
  [ `P of Tm.tm
  | `Def of Tm.tm * Tm.tm
  | `Desc of Desc.desc
  ]

type reexported = (string * Name.t) list

type repo = (string option * entry) list

(* this is not really used, but is useful as an overview

type rot =
  Rot of
    {ver : string;
     deps : dep list;
     reexported : reexported;
     repo : repo}
*)

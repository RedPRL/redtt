open RedTT_Core

let version : string = "It is a person's social being that determines their thinking."

type dep =
  | True
  | False
  | Libsum (* always true, for now *)
  | Self of {stem : FileRes.filepath; redsum : Digest.t}
  | Import of {sel : FileRes.selector; stem : FileRes.filepath; rotsum : Digest.t}
  | Shell of {cmd : string; exit: int}

type entry = GlobalEnv.entry
type rigidity = Unify.rigidity option
type info = entry * rigidity

type reexported = Name.t list

type repo = (string option * info) list

(* this is not really used, but is useful as an overview

type rot =
  Rot of
    {ver : string;
     deps : dep list;
     reexported : reexported;
     repo : repo}
*)

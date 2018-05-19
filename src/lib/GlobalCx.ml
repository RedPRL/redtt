(* TODO *)

open RedBasis
module T = PersistentTable.M
type value = Val.value

type entry =
  {ty : Tm.chk Tm.t;
   tm : Tm.chk Tm.t option}

type t = (string, entry) T.t

let emp = T.init 100

let add_hole sg nm ~ty =
  match T.find nm sg with
  | None ->
    let entry = {ty; el = None} in
    T.set nm entry sg
  | _ ->
    failwith "GlobalCx: name already used"

let define sg nm ~ty ~el =
  match T.find nm sg with
  | None ->
    let entry = {ty; el = Some el} in
    T.set nm entry sg
  | _ ->
    failwith "GlobalCx: name already used"

module M (Sig : sig val globals : t end) : Val.Sig =
struct
  let lookup nm =
    let {ty; tm} = T.get nm Sig.globals in
    match tm with
    | None ->
      Val.Opaque {ty}
    | Some tm ->
      Val.Transparent {tm}

end

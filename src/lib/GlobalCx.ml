(* TODO *)

open RedBasis
module T = PersistentTable.M

type ty = Tm.chk Tm.t
type t = (string, ty) T.t

let emp = T.init 100

let add_hole sg nm ~ty =
  match T.find nm sg with
  | None ->
    T.set nm ty sg
  | _ ->
    failwith "GlobalCx: name already used"

let define sg nm ~ty ~tm =
  match T.find nm sg with
  | None ->
    let face = Tm.make Tm.Dim0, Tm.make Tm.Dim0, Some tm in
    let sys = [face] in
    let rty = Tm.make @@ Tm.Rst {ty; sys} in
    T.set nm rty sg
  | _ ->
    failwith "GlobalCx: name already used"

module M (Sig : sig val globals : t end) : Val.Sig =
struct
  let lookup nm =
    T.get nm Sig.globals
end

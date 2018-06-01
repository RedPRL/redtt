(* TODO *)

open RedBasis
module T = PersistentTable.M

type ty = Tm.tm
type entry = {ty : ty; sys : (Tm.tm, Tm.tm) Tm.system}
type t = (Name.t, entry) T.t

let emp = T.init 100

let ext sg nm ~ty ~sys =
  match T.find nm sg with
  | None ->
    T.set nm {ty; sys} sg
  | _ ->
    failwith "GlobalCx: name already used"

let define sg nm ~ty ~tm =
  match T.find nm sg with
  | None ->
    let face = Tm.make Tm.Dim0, Tm.make Tm.Dim0, Some tm in
    let sys = [face] in
    T.set nm {ty; sys} sg
  | _ ->
    failwith "GlobalCx: name already used"

let lookup_ty sg nm _tw =
  let {ty; _} = T.get nm sg in
  ty

let merge sg0 sg1 =
  T.merge sg0 sg1

module M (Sig : sig val globals : t end) : Val.Sig =
struct
  let lookup nm =
    let {ty; sys} = T.get nm Sig.globals in
    ty, sys
end

type flavor = [`Vars | `RigVars | `Metas]

module Set = Set.Make (Name)

module type S =
sig
  type t
  val free : flavor -> t -> Set.t
end

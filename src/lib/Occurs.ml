type flavor = [`Vars | `RigVars | `Metas]

module Set = Set.Make (Name)

module type S =
sig
  type t
  val free : flavor -> t -> Set.t
end

module List (M : S) : S with type t = M.t list =
struct
  type t = M.t list
  let free fl =
    let rec go xs acc =
      match xs with
      | [] -> acc
      | x::xs ->
        go xs @@
        Set.union acc @@
        M.free fl x
    in
    fun xs ->
      go xs Set.empty
end

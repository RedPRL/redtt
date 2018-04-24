type el = Val.can Val.t
type tm = Tm.chk Tm.t

(** Quote an element of a semantic type as a term. This is defined only for the values of well-typed terms. *)
val quote : int -> ty:el -> el -> tm

(** Take two elements of a semantic type, and quote a canonical representative of the equivalence class;
    if the two elements are not definitionally equal, this throws an exception. *)
val equiv : int -> ty:el -> el -> el -> tm

(** Quote a semantic type as a term. This is defined only for the values of well-formed types. *)
val quote_ty : int -> el -> tm

(** Take two semantic types, and quote a canonical representative of the equivalence class;
    if the two types are not definitionally equal, this throws an exception. *)
val equiv_ty : int -> el -> el -> tm

(** Check if one semantic type is a subtype of the other. *)
val approx_ty : int -> el -> el -> unit

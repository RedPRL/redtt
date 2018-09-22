open Domain

module type Sig =
sig
  val restriction : Restriction.t

  val global_dims : dim DimEnv.t

  (** Return the type and definition of a global variable *)
  val lookup : Name.t -> Tm.twin -> Tm.tm * Tm.tm option

  val lookup_datatype : Desc.data_label -> Tm.data_desc
end

exception MissingElimClause of Desc.con_label

module type S =
sig
  val empty_env : env

  val unleash : value -> con

  val reflect : value -> neu -> val_sys -> value

  val eval : env -> Tm.tm -> value
  val eval_cmd : env -> Tm.tm Tm.cmd -> value
  val eval_head : env -> Tm.tm Tm.head -> value
  val eval_frame : env -> value -> Tm.tm Tm.frame -> value
  val eval_dim : env -> Tm.tm -> I.t
  val eval_tick : env -> Tm.tm -> tick
  val eval_tm_sys : env -> (Tm.tm, Tm.tm) Tm.system -> val_sys

  val make_closure : env -> Tm.tm Tm.bnd -> clo

  val apply : value -> value -> value
  val ext_apply : value -> dim list -> value
  val prev : tick -> value -> value

  val elim_data : Desc.data_label -> mot:clo -> scrut:value -> clauses:(string * nclo) list -> value

  val car : value -> value
  val cdr : value -> value
  val lbl_call : value -> value
  val restriction_force : value -> value

  val rigid_vproj : atom -> func:value -> el:value -> value
  val rigid_cap : dir -> value -> comp_sys -> value -> value
  val rigid_coe : dir -> abs -> value -> value
  val make_coe : dir Dir.m -> abs -> value -> value

  val inst_clo : clo -> value -> value
  val inst_nclo : nclo -> env_el list -> value
  val inst_tick_clo : tick_clo -> tick -> value

  val unleash_pi : value -> value * clo
  val unleash_sg : value -> value * clo
  val unleash_v : value -> atom * value * value * value
  val unleash_later : value -> tick_clo
  val unleash_ext_with : value -> dim list -> value * val_sys
  val unleash_lbl_ty : value -> string * nf list * value
  val unleash_restriction_ty : value -> val_face

  val make_intro : env -> dlbl:Desc.data_label -> clbl:Desc.con_label -> env_el list -> value

  module Sig : Sig

  module Macro : sig
    val equiv : value -> value -> value
    val func : value -> value -> value
  end
end

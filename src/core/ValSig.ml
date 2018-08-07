open Domain

module type Sig =
sig
  val restriction : Restriction.t

  val global_dim : I.atom -> I.t

  (** Return the type and boundary of a global variable *)
  val lookup : Name.t -> Tm.twin -> Tm.tm * (Tm.tm, Tm.tm) Tm.system

  val lookup_datatype : Desc.data_label -> (int, Tm.tm, Tm.tm) Desc.desc
end

module type S =
sig
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

  val eval_bterm : (int, Tm.tm, Tm.tm) Desc.desc -> env -> (int, Tm.tm, Tm.tm) Desc.Boundary.term -> bvalue
  (* val eval_bterm_boundary : (int, Tm.tm, Tm.tm) Desc.desc -> env -> (int, Tm.tm, Tm.tm) Desc.Boundary.sys -> ([`Any], bvalue) face list *)

  val apply : value -> value -> value
  val ext_apply : value -> dim list -> value
  val prev : tick -> value -> value
  val modal_open : value -> value

  val car : value -> value
  val cdr : value -> value
  val lbl_call : value -> value
  val corestriction_force : value -> value

  val rigid_vproj : atom -> ty0:value -> ty1:value -> equiv:value -> el:value -> value

  val inst_clo : clo -> value -> value
  val inst_nclo : nclo -> env_el list -> value
  val inst_tick_clo : tick_clo -> tick -> value

  val unleash_pi : value -> value * clo
  val unleash_sg : value -> value * clo
  val unleash_v : value -> atom * value * value * value
  val unleash_later : value -> tick_clo
  val unleash_box_modality : value -> value
  val unleash_fhcom : value -> dir * value * comp_sys
  val unleash_ext_with : value -> dim list -> value * val_sys
  val unleash_ext : value -> ext_abs
  val unleash_lbl_ty : value -> string * nf list * value
  val unleash_corestriction_ty : value -> val_face

  module Sig : Sig

  module Macro : sig
    val equiv : value -> value -> value
  end
end

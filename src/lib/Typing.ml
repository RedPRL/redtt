module V = Val
module Q = Quote
module T = Tm

type value = V.value

type cx = LocalCx.t

open RedBasis.Bwd


module type S =
sig
  module Cx : LocalCx.S
  val check : cx -> Val.value -> Tm.tm -> unit
  val infer : cx -> Tm.tm Tm.cmd -> value
  val infer_frame : cx -> ty:value -> hd:value -> Tm.tm Tm.frame -> value
  val check_boundary : cx -> Val.value -> Val.val_sys -> Tm.tm -> unit
end

type cofibration = (I.t * I.t) list

module M (Sig : sig val globals : GlobalEnv.t end) =
struct
  module Eval = Val.M (GlobalEnv.M (Sig))
  module Cx = LocalCx.M (Eval)

  let rec check_dim cx tr =
    match T.unleash tr with
    | T.Dim0 ->
      ()
    | T.Dim1 ->
      ()
    | T.Up cmd ->
      check_dim_cmd cx cmd
    | _ ->
      failwith "check_dim: expected dimension"

  and check_dim_cmd cx =
    function
    | hd, Emp ->
      begin
        match hd with
        | Tm.Ix (ix, _) ->
          begin
            match Cx.lookup ix cx with
            | `Dim -> ()
            | _ -> failwith "check_dim_cmd: expected dimension"
          end
        | Tm.Ref _ ->
          (* TODO: lookup in global context, make sure it is a dimension *)
          ()
        | _ -> failwith ""
      end
    | _ ->
      failwith "check_dim_cmd"

  let check_dim_scope oxs r =
    match oxs with
    | None -> ()
    | Some xs ->
      match r with
      | `Atom x ->
        if List.exists (fun y -> x = y) xs then () else failwith "Bad dimension scope"
      | _ -> ()

  let check_valid_cofibration ?xs:(xs = None) cofib =
    let zeros = Hashtbl.create 20 in
    let ones = Hashtbl.create 20 in
    let rec go eqns =
      match eqns with
      | [] -> false
      | (r, r') :: eqns ->
        check_dim_scope xs r;
        check_dim_scope xs r';
        begin
          match I.compare r r' with
          | `Same -> true
          | `Apart -> go eqns
          | `Indet ->
            match r, r' with
            | `Dim0, `Dim1 -> go eqns
            | `Dim1, `Dim0 -> go eqns
            | `Dim0, `Dim0 -> true
            | `Dim1, `Dim1 -> true
            | `Atom x, `Dim0 ->
              if Hashtbl.mem ones x then true else
                begin
                  Hashtbl.add zeros x ();
                  go eqns
                end
            | `Atom x, `Dim1 ->
              if Hashtbl.mem zeros x then true else
                begin
                  Hashtbl.add ones x ();
                  go eqns
                end
            | `Atom x, `Atom y ->
              x = y or go eqns
            | _, _ ->
              go @@ (r', r) :: eqns
        end
    in
    if go cofib then () else failwith "check_valid_cofibration"

  let check_extension_cofibration xs cofib =
    match cofib with
    | [] -> ()
    | _ ->
      check_valid_cofibration ~xs:(Some xs) cofib

  let rec check cx ty tm =
    match Eval.unleash ty, T.unleash tm with
    | V.Univ info0, T.Univ info1 ->
      (* TODO: what about kinds? I think it's fine, since we learned from Andy Pitts how to make
         the pretype universe Kan. But I may need to add those "ecom" thingies, LOL. *)
      if Lvl.greater info0.lvl info1.lvl then () else
        failwith "Predicativity violation"

    | V.Univ _, T.Pi (dom, B (nm, cod)) ->
      let vdom = check_eval cx ty dom in
      let cxx', _ = Cx.ext_ty cx ~nm vdom in
      check cxx' ty cod

    | V.Univ _, T.Sg (dom, B (nm, cod)) ->
      let vdom = check_eval cx ty dom in
      let cxx, _ = Cx.ext_ty cx ~nm vdom in
      check cxx ty cod

    | V.Univ univ, T.Ext (NB (nms, (cod, sys))) ->
      let cxx, xs = Cx.ext_dims cx ~nms in
      let vcod = check_eval cxx ty cod in
      if Kind.lte univ.kind Kind.Kan then
        check_extension_cofibration xs @@ cofibration_of_sys cxx sys
      else
        ();
      check_ext_sys cxx vcod sys

    | V.Univ univ, T.Rst info ->
      if univ.kind = Kind.Pre then () else failwith "Restriction type is not Kan";
      let ty = check_eval cx ty info.ty in
      check_ext_sys cx ty info.sys

    | V.Univ univ, T.CoR (tr, tr', oty) ->
      if univ.kind = Kind.Pre then () else failwith "Co-restriction type is not known to be Kan";
      let r = check_eval_dim cx tr in
      let r' = check_eval_dim cx tr' in
      begin
        match I.compare r r', oty with
        | `Apart, None ->
          ()
        | _, Some ty' ->
          let cxrr' = Cx.restrict cx r r' in
          check cxrr' ty ty'
        | _ ->
          failwith "co-restriction type malformed"
      end

    | V.Univ _, T.V info ->
      check_dim cx info.r;
      let ty0 = check_eval cx ty info.ty0 in
      let ty1 = check_eval cx ty info.ty1 in
      check_is_equivalence cx ~ty0 ~ty1 ~equiv:info.equiv

    | V.Univ _, T.Bool ->
      ()


    | V.Pi {dom; cod}, T.Lam (T.B (nm, tm)) ->
      let cxx, x = Cx.ext_ty cx ~nm dom in
      let vcod = Eval.inst_clo cod x in
      check cxx vcod tm

    | V.Sg {dom; cod}, T.Cons (t0, t1) ->
      let v = check_eval cx dom t0 in
      let vcod = Eval.inst_clo cod v in
      check cx vcod t1

    | V.Ext ext_abs, T.ExtLam (T.NB (nms, tm)) ->
      let cxx, xs = Cx.ext_dims cx ~nms in
      let codx, sysx = Eval.ExtAbs.inst ext_abs @@ List.map (fun x -> `Atom x) xs in
      check_boundary cxx codx sysx tm

    | V.CoR ty_face, T.CoRThunk (tr0, tr1, otm) ->
      let r'0 = check_eval_dim cx tr0 in
      let r'1 = check_eval_dim cx tr1 in
      begin
        match ty_face, otm with
        | IFace.False _, None ->
          ()
        | IFace.True (r0, r1, ty), Some tm ->
          begin
            match I.compare r'0 r0, I.compare r'1 r1 with
            | `Same, `Same ->
              check cx ty tm
            | _ ->
              failwith "co-restriction mismatch"
          end
        | IFace.Indet (p, _), Some tm ->
          let r0, r1 = IStar.unleash p in
          begin
            match I.compare r'0 r0, I.compare r'1 r1 with
            | `Same, `Same ->
              begin
                try
                  let cx' = Cx.restrict cx r'0 r'1 in
                  let phi = I.equate r'0 r'1 in
                  check cx' (Eval.Val.act phi ty) tm
                with
                | Restriction.Inconsistent -> ()
              end
            | _ ->
              failwith "co-restriction mismatch"
          end
        | _ ->
          Format.eprintf "@.@.type restriction didn't match thunk@.@.";
          failwith "Malformed element of co-restriction type"
      end

    | V.Rst {ty; sys}, _ ->
      check cx ty tm;
      check_boundary cx ty sys tm

    | V.Univ _, T.FCom info ->
      check_fcom cx ty info.r info.r' info.cap info.sys

    | V.Univ _, T.LblTy info ->
      check cx ty info.ty;
      let go_arg (ty, tm) =
        let vty = check_eval_ty cx ty in
        check cx vty tm
      in
      ignore @@ List.map go_arg info.args

    | V.LblTy info, T.LblRet t ->
      check cx info.ty t

    | V.Bool, (T.Tt | T.Ff) ->
      ()

    | _, T.Up tm ->
      let ty' = infer cx tm in
      Cx.check_subtype cx ty' ty

    | _, T.Let (cmd, T.B (nm, t1)) ->
      let ty' = infer cx cmd in
      let el = Cx.eval_cmd cx cmd in
      let cx' = Cx.def cx ~nm ~ty:ty' ~el in
      check cx' ty t1

    | _ ->
      (* Format.eprintf "Failed to check term %a@." (Tm.pp (Cx.ppenv cx)) tm; *)
      failwith "Type error"

  and cofibration_of_sys : type a. cx -> (Tm.tm, a) Tm.system -> cofibration =
    fun cx sys ->
      let face (tr, tr', _) =
        let r = Cx.eval_dim cx tr in
        let r' = Cx.eval_dim cx tr' in
        (r, r')
      in
      List.map face sys

  and check_fcom cx ty tr tr' tcap tsys =
    let r = check_eval_dim cx tr in
    check_dim cx tr';
    let cxx, x = Cx.ext_dim cx ~nm:None in
    let cap = check_eval cx ty tcap in
    check_valid_cofibration @@ cofibration_of_sys cx tsys;
    check_comp_sys cx r (cxx, x, ty) cap tsys

  and check_boundary cx ty sys tm =
    let rec go sys =
      match sys with
      | [] -> ()
      | face :: sys ->
        check_boundary_face cx ty face tm;
        go sys
    in
    check cx ty tm;
    go sys

  and check_boundary_face cx ty face tm =
    match face with
    | IFace.True (_, _, el) ->
      Cx.check_eq cx ~ty el @@
      Cx.eval cx tm

    | IFace.False _ ->
      ()

    | IFace.Indet (p, el) ->
      let r, r' = IStar.unleash p in
      try
        let cx' = Cx.restrict cx r r' in
        let phi = I.equate r r' in
        Cx.check_eq cx' ~ty:(Eval.Val.act phi ty) el @@
        Cx.eval cx' tm
      with
      | (Restriction.Inconsistent | I.Inconsistent) ->
        ()
      | exn ->
        (* Format.eprintf "%a %a   Failed with %s@." I.pp r I.pp r' (Printexc.to_string exn); *)
        raise exn


  and check_ext_sys cx ty sys =
    let rec go sys acc =
      match sys with
      | [] ->
        ()
      | (tr0, tr1, otm) :: sys ->
        let r0 = check_eval_dim cx tr0 in
        let r1 = check_eval_dim cx tr1 in
        begin
          match I.compare r0 r1, otm with
          | `Apart, _ ->
            go sys acc

          | (`Same | `Indet), Some tm ->
            begin
              try
                let phi = I.equate r0 r1 in
                let cx' = Cx.restrict cx r0 r1 in
                check cx' (Eval.Val.act phi ty) tm;

                (* Check face-face adjacency conditions *)
                go_adj cx' acc (r0, r1, tm)
              with
              | (I.Inconsistent | Restriction.Inconsistent) -> ()
            end;
            go sys @@ (r0, r1, tm) :: acc

          | _, None ->
            failwith "check_ext_sys"
        end

    and go_adj cx faces face =
      match faces with
      | [] -> ()
      | (r'0, r'1, tm') :: faces ->
        (* Invariant: cx should already be restricted by r0=r1 *)
        let r0, r1, tm = face in
        begin
          try
            let cx' = Cx.restrict cx r'0 r'1 in
            let v = Cx.eval cx' tm in
            let v' = Cx.eval cx' tm' in
            let phi = I.cmp (I.equate r'0 r'1) (I.equate r0 r1) in
            Cx.check_eq cx' ~ty:(Eval.Val.act phi ty) v v'
          with
          | (I.Inconsistent | Restriction.Inconsistent) -> ()
        end;
        go_adj cx faces face
    in
    go sys []

  and check_comp_sys cx r (cxx, x, tyx) cap sys =
    let rec go sys acc =
      match sys with
      | [] ->
        ()
      | (tr0, tr1, obnd) :: sys ->
        let r0 = check_eval_dim cx tr0 in
        let r1 = check_eval_dim cx tr1 in
        begin
          match I.compare r0 r1, obnd with
          | `Apart, _ ->
            go sys acc

          | (`Same | `Indet), Some bnd ->
            begin
              try
                (* check that bnd is a section of tyx under r0=r1 *)
                let cxxr0r1 = Cx.restrict cxx r0 r1 in
                let phir0r1 = I.equate r0 r1 in
                let T.B (_, tm) = bnd in
                check cxxr0r1 (Eval.Val.act phir0r1 tyx) tm;

                (* check that tm<r/x> = cap under r0=r1 *)
                let cxr0r1 = Cx.restrict cx r0 r1 in
                let phirx = I.cmp phir0r1 @@ I.subst r x in
                Cx.check_eq cxr0r1
                  ~ty:(Eval.Val.act phirx tyx)
                  (Eval.Val.act phir0r1 cap)
                  (Eval.Val.act phirx cap);

                (* Check face-face adjacency conditions *)
                go_adj cxxr0r1 acc (r0, r1, bnd)
              with
                (I.Inconsistent | Restriction.Inconsistent)-> ()
            end;

            go sys @@ (r0, r1, bnd) :: acc

          | _, None ->
            failwith "check_comp_sys"
        end

    and go_adj cxx faces face =
      match faces with
      | [] -> ()
      | (r'0, r'1, bnd') :: faces ->
        let T.B (_, tm') = bnd' in
        (* Invariant: cx should already be restricted by r0=r1 *)
        let r0, r1, bnd = face in
        let T.B (_, tm) = bnd in
        begin
          try
            let cxx' = Cx.restrict cxx r'0 r'1 in
            let v = Cx.eval cxx' tm in
            let v' = Cx.eval cxx' tm' in
            let phi = I.cmp (I.equate r'0 r'1) (I.equate r0 r1) in
            Cx.check_eq cxx' ~ty:(Eval.Val.act phi tyx) v v'
          with
          | (I.Inconsistent | Restriction.Inconsistent) -> ()
        end;
        go_adj cxx faces face

    in go sys []

  and infer cx (hd, sp) =
    let ty_hd = infer_head cx hd in
    let vhd = Cx.eval_head cx hd in
    infer_stack cx ~ty:ty_hd ~hd:vhd @@ Bwd.to_list sp
  (* TODO: should just write inference directly for spines ! *)

  and infer_stack cx ~ty ~hd =
    function
    | [] -> ty
    | frm :: stk ->
      let ty = infer_frame cx ~ty ~hd frm in
      let hd = Cx.eval_frame cx hd frm in
      infer_stack cx ~ty ~hd stk

  and infer_frame cx ~ty ~hd =
    function
    | T.Car ->
      let dom, _ = Eval.unleash_sg ~debug:["infer-frame/car"] ty in
      dom

    | T.Cdr ->
      let _, cod = Eval.unleash_sg ty in
      Eval.inst_clo cod @@ Eval.car hd

    | T.FunApp t ->
      let dom, cod = Eval.unleash_pi ~debug:["infer_frame"] ty in
      let v = check_eval cx dom t in
      Eval.inst_clo cod v

    | T.ExtApp ts ->
      let rs = List.map (check_eval_dim cx) ts in
      let ty, _ = Eval.unleash_ext ty rs in
      ty

    | T.VProj info ->
      let v_ty =
        check_eval_ty cx @@
        T.make @@ T.V {r = info.r; ty0 = info.ty0; ty1 = info.ty1; equiv = info.equiv}
      in
      Cx.check_eq_ty cx v_ty ty;
      Cx.eval cx info.ty1

    | T.If info ->
      let T.B (nm, mot) = info.mot in
      let bool = Eval.make V.Bool in
      let cxx, _= Cx.ext_ty cx ~nm bool in
      check_ty cxx mot;

      Cx.check_eq_ty cx ty bool;

      let cx_tt = Cx.def cx ~nm ~ty:bool ~el:(Eval.make V.Tt) in
      let cx_ff = Cx.def cx ~nm ~ty:bool ~el:(Eval.make V.Ff) in
      let mot_tt = Cx.eval cx_tt mot in
      let mot_ff = Cx.eval cx_ff mot in
      check cx mot_tt info.tcase;
      check cx mot_ff info.fcase;

      let cx_scrut = Cx.def cx ~nm ~ty:bool ~el:hd in
      Cx.eval cx_scrut mot

    | T.S1Rec info ->
      let T.B (nm, mot) = info.mot in
      let s1 = Eval.make V.S1 in
      let cxx, _= Cx.ext_ty cx ~nm s1 in
      check_ty cxx mot;

      Cx.check_eq_ty cx ty s1;

      let cx_base = Cx.def cx ~nm ~ty:s1 ~el:(Eval.make V.Base) in
      let mot_base = Cx.eval cx_base mot in
      let val_base = check_eval cx mot_base info.bcase in

      let T.B (nm_loop, lcase) = info.lcase in
      let cxx, x = Cx.ext_dim cx ~nm:nm_loop in
      let cxx_loop = Cx.def cxx ~nm ~ty:s1 ~el:(Eval.make @@ V.Loop x) in
      let mot_loop = Cx.eval cxx_loop mot in
      let val_loopx = check_eval cx mot_loop lcase in
      let val_loop0 = Eval.Val.act (I.subst `Dim0 x) val_loopx in
      let val_loop1 = Eval.Val.act (I.subst `Dim1 x) val_loopx in
      Cx.check_eq cx mot_base val_loop0 val_base;
      Cx.check_eq cx mot_base val_loop1 val_base;

      let cx_scrut = Cx.def cx ~nm ~ty:s1 ~el:hd in
      Cx.eval cx_scrut mot

    | T.LblCall ->
      let _, _, ty = Eval.unleash_lbl_ty ty in
      ty

    | Tm.CoRForce ->
      begin
        match Eval.unleash_corestriction_ty ty with
        | IFace.True (_, _, ty) -> ty
        | _ -> failwith "Cannot force co-restriction when it is not true!"
      end

  and infer_head cx =
    function
    | T.Ref {name; twin; ushift} ->
      let ty = Tm.shift_univ ushift @@ GlobalEnv.lookup_ty Sig.globals name twin in
      Cx.eval Cx.emp ty

    | T.Ix (ix, _) ->
      begin
        match Cx.lookup ix cx with
        | `Ty ty -> ty
        | `Dim -> failwith "infer: expected type hypothesis"
      end

    | T.Meta {name; ushift} ->
      let ty = Tm.shift_univ ushift @@ GlobalEnv.lookup_ty Sig.globals name `Only in
      Cx.eval Cx.emp ty

    | T.Coe info ->
      let r = check_eval_dim cx info.r in
      let r' = check_eval_dim cx info.r' in
      let T.B (nm, ty) = info.ty in
      let cxx, x = Cx.ext_dim cx ~nm in
      let vtyx = check_eval_ty cxx ty in
      let vtyr = Eval.Val.act (I.subst r x) vtyx in
      check cx vtyr info.tm;
      Eval.Val.act (I.subst r' x) vtyx

    | T.Com info ->
      let r = check_eval_dim cx info.r in
      let r' = check_eval_dim cx info.r' in
      let T.B (nm, ty) = info.ty in
      let cxx, x = Cx.ext_dim cx ~nm in
      let vtyx = check_eval_ty cxx ty in
      let vtyr = Eval.Val.act (I.subst r x) vtyx in
      let cap = check_eval cx vtyr info.cap in
      check_comp_sys cx r (cxx, x, vtyx) cap info.sys;
      Eval.Val.act (I.subst r' x) vtyx

    | T.HCom info ->
      let r = check_eval_dim cx info.r in
      check_dim cx info.r';
      let cxx, x = Cx.ext_dim cx ~nm:None in
      let vty = check_eval_ty cx info.ty in
      let cap = check_eval cx vty info.cap in
      check_valid_cofibration @@ cofibration_of_sys cx info.sys;
      check_comp_sys cx r (cxx, x, vty) cap info.sys;
      vty

    | T.Down info ->
      let ty = check_eval_ty cx info.ty in
      check cx ty info.tm;
      ty


  and check_eval cx ty tm =
    check cx ty tm;
    Cx.eval cx tm

  and check_ty cx ty =
    let univ = Eval.make @@ V.Univ {kind = Kind.Pre; lvl = Lvl.Omega} in
    check cx univ ty

  and check_eval_dim cx tr =
    check_dim cx tr;
    Cx.eval_dim cx tr

  and check_eval_ty cx ty =
    check_ty cx ty;
    Cx.eval cx ty

  and check_is_equivalence cx ~ty0 ~ty1 ~equiv =
    let type_of_equiv = Eval.Macro.equiv ty0 ty1 in
    check cx type_of_equiv equiv
end


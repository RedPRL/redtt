module V = Val
module Q = Quote
module T = Tm
module R = Restriction

type value = V.value

type cx = LocalCx.t

open RedBasis.Bwd


module type S =
sig
  module Cx : LocalCx.S
  val check : cx -> Val.value -> Tm.tm -> unit
  val infer : cx -> Tm.tm Tm.cmd -> value
  val check_boundary : cx -> Val.value -> Val.val_sys -> Tm.tm -> unit
end


type cofibration = (R.dim * R.dim) list

module M (Sig : sig val globals : GlobalCx.t end) =
struct
  module Eval = Val.M (GlobalCx.M (Sig))
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
    | Tm.Cut (hd, Emp) ->
      begin
        match hd with
        | Tm.Ix (ix, _) ->
          begin
            match Cx.lookup ix cx with
            | `Dim -> ()
            | _ -> failwith "check_dim_cmd: expected dimension"
          end
        | Tm.Ref (_a, _) ->
          (* TODO: lookup in global context, make sure it is a dimension *)
          ()
        | _ -> failwith ""
      end
    | _ ->
      failwith "check_dim_cmd"

  let check_dim_in_class cx ocls r : unit =
    match ocls with
    | None -> ()
    | Some cls ->
      let clr = Cx.unleash_dim cx r in
      begin
        match Dim.compare cls clr with
        | Dim.Same ->
          ()
        | _ ->
          Format.printf "check_dim_in_class: %a in %a@." Dim.pp clr Dim.pp cls;
          failwith "check_dim_in_class"
      end

  let check_valid_cofibration cx ?dim_cls:(dim_cls = None) cofib =
    let zeros = Hashtbl.create 20 in
    let ones = Hashtbl.create 20 in
    let rec go eqns =
      match eqns with
      | [] -> false
      | (r, r') :: eqns ->
        check_dim_in_class cx dim_cls r;
        check_dim_in_class cx dim_cls r';
        begin
          match Cx.compare_dim cx r r' with
          | Dim.Same -> true
          | Dim.Apart -> go eqns
          | Dim.Indeterminate ->
            match r, r' with
            | Dim.Dim0, Dim.Dim1 -> go eqns
            | Dim.Dim1, Dim.Dim0 -> go eqns
            | Dim.Dim0, Dim.Dim0 -> true
            | Dim.Dim1, Dim.Dim1 -> true
            | Dim.Atom x, Dim.Dim0 ->
              if Hashtbl.mem ones x then true else
                begin
                  Hashtbl.add zeros x ();
                  go eqns
                end
            | Dim.Atom x, Dim.Dim1 ->
              if Hashtbl.mem zeros x then true else
                begin
                  Hashtbl.add ones x ();
                  go eqns
                end
            | Dim.Atom x, Dim.Atom y ->
              x = y or go eqns
            | _, _ ->
              go @@ (r', r) :: eqns
        end
    in
    if go cofib then () else failwith "check_valid_cofibration"

  let check_extension_cofibration cx xs cofib =
    match cofib, xs with
    | [], _ -> ()
    | _, x :: xs ->
      let dim_of_atom x = Dim.Atom x in
      let cls = Dim.from_reprs (dim_of_atom x) @@ Dim.Dim0 :: Dim.Dim1 :: dim_of_atom x :: List.map dim_of_atom xs in
      check_valid_cofibration cx ~dim_cls:(Some cls) cofib
    | _ ->
      failwith "check_extension_cofibration"

  let rec check cx ty tm =
    match Eval.unleash ty, T.unleash tm with
    | V.Univ info0, T.Univ info1 ->
      (* TODO: what about kinds? I think it's fine, since we learned from Andy Pitts how to make
         the pretype universe Kan. But I may need to add those "ecom" fuckers, LOL. *)
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
      if not @@ Kind.stronger Kind.Kan univ.kind then
        check_extension_cofibration cx xs @@ cofibration_of_sys cxx sys
      else
        ();
      check_ext_sys cxx vcod sys

    | V.Univ univ, T.Rst info ->
      if univ.kind = Kind.Pre then () else failwith "Restriction type is not Kan";
      let ty = check_eval cx ty info.ty in
      check_ext_sys cx ty info.sys

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
      let codx, sysx = Eval.ExtAbs.inst ext_abs @@ List.map Dim.named xs in
      check_boundary cxx codx sysx tm

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
      Format.eprintf "Failed to check term %a@." (Tm.pp (Cx.ppenv cx)) tm;
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
    check_valid_cofibration cx @@ cofibration_of_sys cx tsys;
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
    | Face.True (_, _, el) ->
      Cx.check_eq cx ~ty el @@
      Cx.eval cx tm

    | Face.False _ ->
      ()

    | Face.Indet (p, el) ->
      let r, r' = DimStar.unleash p in
      let cx' = Cx.restrict cx (Dim.unleash r) (Dim.unleash r') in
      let phi = Dim.equate r r' in
      Cx.check_eq cx' ~ty:(Eval.Val.act phi ty) el @@
      Cx.eval cx' tm

  and check_ext_sys cx ty sys =
    let rec go sys acc =
      match sys with
      | [] ->
        ()
      | (tr0, tr1, otm) :: sys ->
        let r0 = check_eval_dim cx tr0 in
        let r1 = check_eval_dim cx tr1 in
        begin
          match Cx.compare_dim cx r0 r1, otm with
          | Dim.Apart, None ->
            go sys acc

          | (Dim.Same | Dim.Indeterminate), Some tm ->
            begin
              try
                let phi = Cx.equate_dim cx r0 r1 in
                let cx' = Cx.restrict cx r0 r1 in
                check cx' (Eval.Val.act phi ty) tm;

                (* Check face-face adjacency conditions *)
                go_adj cx' acc (r0, r1, tm)
              with
              | R.Inconsistent -> ()
            end;
            go sys @@ (r0, r1, tm) :: acc

          | _ ->
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
            let phi = Dim.cmp (Cx.equate_dim cx r'0 r'1) (Cx.equate_dim cx r0 r1) in
            Cx.check_eq cx' ~ty:(Eval.Val.act phi ty) v v'
          with
          | R.Inconsistent -> ()
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
          match Cx.compare_dim cx r0 r1, obnd with
          | Dim.Apart, None ->
            go sys acc

          | (Dim.Same | Dim.Indeterminate), Some bnd ->
            begin
              try
                (* check that bnd is a section of tyx under r0=r1 *)
                let cxxr0r1 = Cx.restrict cxx r0 r1 in
                let phir0r1 = Dim.equate (Dim.singleton r0) (Dim.singleton r1) in
                let T.B (_, tm) = bnd in
                check cxxr0r1 (Eval.Val.act phir0r1 tyx) tm;

                (* check that tm<r/x> = cap under r0=r1 *)
                let cxr0r1 = Cx.restrict cx r0 r1 in
                let phirx = Dim.cmp phir0r1 @@ Dim.subst (Dim.singleton r) x in
                Cx.check_eq cxr0r1
                  ~ty:(Eval.Val.act phirx tyx)
                  (Eval.Val.act phir0r1 cap)
                  (Eval.Val.act phirx cap);

                (* Check face-face adjacency conditions *)
                go_adj cxxr0r1 acc (r0, r1, bnd)
              with
                R.Inconsistent -> ()
            end;

            go sys @@ (r0, r1, bnd) :: acc

          | _ ->
            failwith "check_ext_sys"
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
            let phi = Dim.cmp (Dim.equate (Dim.singleton r'0) (Dim.singleton r'1)) (Dim.equate (Dim.singleton r0) (Dim.singleton r1)) in
            Cx.check_eq cxx' ~ty:(Eval.Val.act phi tyx) v v'
          with
          | R.Inconsistent -> ()
        end;
        go_adj cxx faces face

    in go sys []

  and infer cx =
    function Cut (hd, sp) ->
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
      let dom, _ = Eval.unleash_sg ty in
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
      let ty, _ = Eval.unleash_ext ty @@ List.map (Cx.unleash_dim cx) rs in
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

    | T.LblCall ->
      let _, _, ty = Eval.unleash_lbl_ty ty in
      ty

  and infer_head cx =
    function
    | T.Ref (name, tw) ->
      let ty = GlobalCx.lookup_ty Sig.globals name tw in
      Cx.eval Cx.emp ty

    | T.Ix (ix, _) ->
      begin
        (* TODO: account for twins *)
        match Cx.lookup ix cx with
        | `Ty ty -> ty
        | `Dim -> failwith "infer: expected type hypothesis"
      end

    | T.Meta name ->
      let ty = GlobalCx.lookup_ty Sig.globals name `Only in
      Cx.eval Cx.emp ty

    | T.Coe info ->
      let r = check_eval_dim cx info.r in
      let r' = check_eval_dim cx info.r' in
      let T.B (nm, ty) = info.ty in
      let cxx, x = Cx.ext_dim cx ~nm in
      let vtyx = check_eval_ty cxx ty in
      let vtyr = Eval.Val.act (Dim.subst (Cx.unleash_dim cx r) x) vtyx in
      check cx vtyr info.tm;
      Eval.Val.act (Dim.subst (Cx.unleash_dim cx r') x) vtyx

    | T.Com info ->
      let r = check_eval_dim cx info.r in
      let r' = check_eval_dim cx info.r' in
      let T.B (nm, ty) = info.ty in
      let cxx, x = Cx.ext_dim cx ~nm in
      let vtyx = check_eval_ty cxx ty in
      let vtyr = Eval.Val.act (Dim.subst (Dim.singleton r) x) vtyx in
      let cap = check_eval cx vtyr info.cap in
      check_comp_sys cx r (cxx, x, vtyx) cap info.sys;
      Eval.Val.act (Dim.subst (Dim.singleton r') x) vtyx

    | T.HCom info ->
      let r = check_eval_dim cx info.r in
      check_dim cx info.r';
      let cxx, x = Cx.ext_dim cx ~nm:None in
      let vty = check_eval_ty cx info.ty in
      let cap = check_eval cx vty info.cap in
      check_valid_cofibration cx @@ cofibration_of_sys cx info.sys;
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

  and check_eval_dim cx tr : Dim.repr =
    check_dim cx tr;
    Cx.eval_dim cx tr

  and check_eval_ty cx ty =
    check_ty cx ty;
    Cx.eval cx ty

  and check_is_equivalence cx ~ty0 ~ty1 ~equiv =
    let type_of_equiv = Eval.Macro.equiv ty0 ty1 in
    check cx type_of_equiv equiv
end

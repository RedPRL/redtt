open RedBasis
open Bwd

type cx = LocalCx.t
type value = Val.value
type cofibration = (I.t * I.t) list

type constraint_ =
  | ChkEq of cx * value * (value * value)

type _ judgment =
  | Chk : cx * value * Tm.tm -> unit judgment
  | Constrain : constraint_ -> unit judgment
  | Eval : cx * Tm.tm -> value judgment

module type Cont =
sig
  include Monad.S
  type ('a, 'b) cont = (module LocalCx.S) -> 'a -> 'b m

  val get_cx : (module LocalCx.S) m
  val callcc : (('a, 'b) cont -> 'a m) -> 'a m
  val run : (module LocalCx.S) -> 'a m -> [`Ok | `Interrupt of constraint_ * (unit, unit) cont]

  val interrupt : constraint_ -> (unit, unit) cont -> 'a m
end

module Cont : Cont =
struct
  type 'a m = (module LocalCx.S) -> ((module LocalCx.S) -> 'a -> unit) -> unit
  type ('a, 'b) cont = (module LocalCx.S) -> 'a -> 'b m

  let ret x cx k =
    k cx x

  let get_cx : (module LocalCx.S) m =
    fun cx k ->
      k cx cx

  let bind (m : 'a m) (f : 'a -> 'b m) : 'b m =
    fun cx cont ->
      m cx @@ fun cx x ->
      f x cx cont

  let callcc (k : ('a, 'b) cont -> 'a m) : 'a m =
    fun cx cont ->
      (* TODO: make sure I'm passing the right cx' *)
      k (fun cx' x _ _ -> cont cx' x) cx cont

  exception Interrupt of constraint_ * (unit, unit) cont

  let run (module Cx : LocalCx.S) (m : 'a m) =
    try
      m (module Cx) (fun _ _ -> ());
      `Ok
    with
    | Interrupt (ctr, kont) ->
      `Interrupt (ctr, kont)
  let interrupt ctr k =
    raise @@ Interrupt (ctr, k)

end


type error =
  | PredicativityViolation
  | ExpectedDimension of cx * Tm.tm

exception E of error


module T = Tm
module V = Val


module Notation = Monad.Notation (Cont)
open Cont open Notation

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
            x = y || go eqns
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

let cofibration_of_sys : type a. cx -> (Tm.tm, a) Tm.system -> cofibration m =
  fun cx sys ->
    get_cx >>= fun (module Cx) ->
    let face (tr, tr', _) =
      let r = Cx.eval_dim cx tr in
      let r' = Cx.eval_dim cx tr' in
      (r, r')
    in
    ret @@ List.map face sys


let chk_dim_cmd cx =
  function
  | hd, Emp ->
    begin
      match hd with
      | Tm.Ix (ix, _) ->
        begin
          get_cx >>= fun (module Cx) ->
          match Cx.lookup ix cx with
          | `Dim ->
            ret ()
          | _ ->
            raise @@ E (ExpectedDimension (cx, T.up (hd, Emp)))
        end
      | Tm.Var _ ->
        (* TODO: lookup in global context, make sure it is a dimension *)
        ret ()
      | _ ->
        raise @@ E (ExpectedDimension (cx, T.up (hd, Emp)))
    end
  | _ ->
    failwith "check_dim_cmd"

let rec chk_dim cx tr =
  match T.unleash tr with
  | T.Dim0 ->
    ret ()
  | T.Dim1 ->
    ret ()
  | T.Up cmd ->
    chk_dim_cmd cx cmd
  | _ ->
    raise @@ E (ExpectedDimension (cx, tr))

let chk_eval_dim cx tr =
  chk_dim cx tr >>
  get_cx >>= fun (module Cx) ->
  ret @@ Cx.eval_dim cx tr


let rec chk cx ty tm =
  get_cx >>= fun (module Cx) ->
  match Cx.Eval.unleash ty, T.unleash tm with
  | V.Univ info0, T.Univ info1 ->
    if Lvl.greater info0.lvl info1.lvl then ret () else
      raise @@ E PredicativityViolation

  | V.Univ _, T.Pi (dom, B (nm, cod)) ->
    chk_eval cx ty dom >>= fun vdom ->
    let cxx, _ = Cx.ext_ty cx ~nm vdom in
    chk cxx ty cod

  | V.Univ _, T.Sg (dom, B (nm, cod)) ->
    chk_eval cx ty dom >>= fun vdom ->
    let cxx, _ = Cx.ext_ty cx ~nm vdom in
    chk cxx ty cod

  | V.Univ univ, T.Ext (NB (nms, (cod, sys))) ->
    let cxx, xs = Cx.ext_dims cx ~nms:(Bwd.to_list nms) in
    chk_eval cxx ty cod >>= fun vcod ->
    begin
      if Kind.lte univ.kind Kind.Kan then
        cofibration_of_sys cxx sys >>= fun cofib ->
        ret @@ check_extension_cofibration xs cofib
      else
        ret ()
    end >>
    chk_ext_sys cxx vcod sys

  | _ ->
    failwith "TODO"


and chk_ext_sys cx ty sys =
  let rec go sys acc =
    match sys with
    | [] ->
      ret ()
    | (tr0, tr1, otm) :: sys ->
      chk_eval_dim cx tr0 >>= fun r0 ->
      chk_eval_dim cx tr1 >>= fun r1 ->
      begin
        match I.compare r0 r1, otm with
        | `Apart, _ ->
          go sys acc

        | (`Same | `Indet), Some tm ->
          begin
            get_cx >>= fun (module Cx) ->
            try
              let cx', phi = Cx.restrict cx r0 r1 in
              chk cx' (Cx.Eval.Val.act phi ty) tm >>
              go_adj cx' acc (r0, r1, tm)
            with
            | I.Inconsistent ->
              ret ()
          end

        | _, None ->
          failwith "check_ext_sys"
      end

  and go_adj cx faces face =
    match faces with
    | [] ->
      ret ()
    | (r'0, r'1, tm') :: faces ->
      let r0, r1, tm = face in
      begin
        get_cx >>= fun (module Cx) ->
        try
          let cx', phi = Cx.restrict cx r'0 r'1 in
          let v = Cx.eval cx' tm in
          let v' = Cx.eval cx' tm' in
          let phi = I.cmp phi (I.equate r0 r1) in
          chk_eq cx' ~ty:(Cx.Eval.Val.act phi ty) v v'
        with
        | I.Inconsistent ->
          ret ()
      end >>
      go_adj cx faces face
  in
  go sys []


and chk_eval cx ty tm =
  chk cx ty tm >>= fun _ ->
  get_cx >>= fun (module Cx) ->
  ret @@ Cx.eval cx tm

and chk_eq cx ~ty el0 el1 =
  constrain @@ ChkEq (cx, ty, (el0, el1))

and constrain ctr =
  callcc @@ fun kont ->
  get_cx >>= fun (module Cx) ->
  match ctr with
  | ChkEq (cx, ty, (el0, el1)) ->
    callcc @@ fun kont ->
    try
      Cx.check_eq cx ~ty el0 el1;
      ret ()
    with
    | _  ->
      interrupt ctr kont




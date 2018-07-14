open RedBasis
open Bwd
open BwdNotation

type twin = [`Only | `TwinL | `TwinR]

type 'a bnd = B of string option * 'a
type 'a nbnd = NB of string option bwd * 'a

type ('r, 'a) face = 'r * 'r * 'a option
type ('r, 'a) system = ('r, 'a) face list

type 'a tmf =
  | FCom of {r : 'a; r' : 'a; cap : 'a; sys : ('a, 'a bnd) system}

  | Univ of {kind : Kind.t; lvl : Lvl.t}
  | Pi of 'a * 'a bnd
  | Ext of ('a * ('a, 'a) system) nbnd
  | Rst of {ty : 'a; sys : ('a, 'a) system}
  | CoR of ('a, 'a) face
  | Sg of 'a * 'a bnd

  | V of {r : 'a; ty0 : 'a; ty1 : 'a; equiv : 'a}
  | VIn of {r : 'a; tm0 : 'a; tm1 : 'a}

  | Bool
  | Tt
  | Ff

  | Nat
  | Zero
  | Suc of 'a

  | Int
  | Pos of 'a
  | NegSuc of 'a

  | S1
  | Base
  | Loop of 'a

  | Lam of 'a bnd
  | ExtLam of 'a nbnd
  | CoRThunk of ('a, 'a) face

  | Cons of 'a * 'a
  | Dim0
  | Dim1

  | Box of {r : 'a; r' : 'a; cap : 'a; sys : ('a, 'a) system}

  (* Labelled types from Epigram *)
  | LblTy of {lbl : string; args : ('a * 'a) list; ty : 'a}
  | LblRet of 'a

  | Up of 'a cmd
  | Let of 'a cmd * 'a bnd

and 'a head =
  | Meta of {name: Name.t; ushift : int}
  | Var of {name : Name.t; twin : twin; ushift : int}
  | Ix of int * twin
  | Down of {ty : 'a; tm : 'a}
  | Coe of {r : 'a; r' : 'a; ty : 'a bnd; tm : 'a}
  | HCom of {r : 'a; r' : 'a; ty : 'a; cap : 'a; sys : ('a, 'a bnd) system}
  | Com of {r : 'a; r' : 'a; ty : 'a bnd; cap : 'a; sys : ('a, 'a bnd) system}
  | GHCom of {r : 'a; r' : 'a; ty : 'a; cap : 'a; sys : ('a, 'a bnd) system}
  | GCom of {r : 'a; r' : 'a; ty : 'a bnd; cap : 'a; sys : ('a, 'a bnd) system}


and 'a frame =
  | Car
  | Cdr
  | FunApp of 'a
  | ExtApp of 'a bwd
  | If of {mot : 'a bnd; tcase : 'a; fcase : 'a}
  | NatRec of {mot : 'a bnd; zcase : 'a; scase : 'a nbnd}
  | IntRec of {mot : 'a bnd; pcase : 'a bnd; ncase : 'a bnd}
  | S1Rec of {mot : 'a bnd; bcase : 'a; lcase : 'a bnd}
  | VProj of {r : 'a; ty0 : 'a; ty1 : 'a; equiv : 'a}
  | Cap of {r : 'a; r' : 'a; ty : 'a; sys : ('a, 'a bnd) system}
  | LblCall
  | CoRForce

and 'a spine = 'a frame bwd
and 'a cmd = 'a head * 'a spine


type 'a subst =
  | Shift of int
  | Dot of 'a * 'a subst
  | Lift of int * 'a subst

type tm = Tm of tm tmf

type error =
  | InvalidDeBruijnIndex of int
  | UnbindExtLengthMismatch of Name.t list * (tm * (tm, tm) system) nbnd

exception E of error

let ix ?twin:(tw = `Only) i =
  Ix (i, tw), Emp

let var ?twin:(tw = `Only) a =
  Var {name = a; twin = tw; ushift = 0}, Emp



module type Alg =
sig
  module M : Monad.S
  val push_bindings : int -> 'a M.m -> 'a M.m
  val under_meta : 'a M.m -> 'a M.m

  val bvar : ih:(tm cmd -> tm cmd M.m) -> ix:int -> twin:twin -> tm cmd M.m
  val fvar : name:Name.t -> twin:twin -> ushift:int -> tm cmd M.m
  val meta : name:Name.t -> ushift:int -> tm cmd M.m
end

module Traverse (A : Alg) : sig
  val traverse_tm : tm -> tm A.M.m
  val traverse_spine : tm spine -> tm spine A.M.m
end =
struct
  module M = A.M
  module Notation = Monad.Notation (M)
  open Notation

  let rec traverse_tm (Tm con) =
    traverse_con con >>= fun con' ->
    M.ret @@ Tm con'

  and traverse_con =
    function
    | (Univ _ | Tt | Ff | Bool | S1 | Nat | Int | Dim0 | Dim1 | Base | Zero as con) ->
      M.ret con

    | FCom info ->
      traverse_tm info.r >>= fun r ->
      traverse_tm info.r' >>= fun r' ->
      traverse_tm info.cap >>= fun cap ->
      traverse_list traverse_bface info.sys >>= fun sys ->
      M.ret @@ FCom {r; r'; cap; sys}

    | Pi (dom, cod) ->
      traverse_tm dom >>= fun dom' ->
      traverse_bnd traverse_tm cod >>= fun cod' ->
      M.ret @@ Pi (dom', cod')

    | Sg (dom, cod) ->
      traverse_tm dom >>= fun dom' ->
      traverse_bnd traverse_tm cod >>= fun cod' ->
      M.ret @@ Sg (dom', cod')

    | Ext ebnd ->
      traverse_nbnd
        (traverse_pair traverse_tm (traverse_list traverse_face))
        ebnd
      >>= fun ebnd' ->
      M.ret @@ Ext ebnd'

    | Rst info ->
      traverse_tm info.ty >>= fun ty ->
      traverse_list traverse_face info.sys >>= fun sys ->
      M.ret @@ Rst {ty; sys}

    | CoR face ->
      traverse_face face >>= fun face' ->
      M.ret @@ CoR face'

    | Cons (t0, t1) ->
      traverse_tm t0 >>= fun t0' ->
      traverse_tm t1 >>= fun t1' ->
      M.ret @@ Cons (t0', t1')

    | V info ->
      traverse_tm info.r >>= fun r ->
      traverse_tm info.ty0 >>= fun ty0 ->
      traverse_tm info.ty1 >>= fun ty1 ->
      traverse_tm info.equiv >>= fun equiv ->
      M.ret @@ V {r; ty0; ty1; equiv}

    | VIn info ->
      traverse_tm info.r >>= fun r ->
      traverse_tm info.tm0 >>= fun tm0 ->
      traverse_tm info.tm1 >>= fun tm1 ->
      M.ret @@ VIn {r; tm0; tm1}

    | Suc t ->
      traverse_tm t >>= fun t' ->
      M.ret @@ Suc t'

    | NegSuc t ->
      traverse_tm t >>= fun t' ->
      M.ret @@ NegSuc t'

    | Pos t ->
      traverse_tm t >>= fun t' ->
      M.ret @@ Pos t'

    | Loop r ->
      traverse_tm r >>= fun r' ->
      M.ret @@ Loop r'

    | Lam bnd ->
      traverse_bnd traverse_tm bnd >>= fun bnd' ->
      M.ret @@ Lam bnd'

    | ExtLam nbnd ->
      traverse_nbnd traverse_tm nbnd >>= fun nbnd' ->
      M.ret @@ ExtLam nbnd'

    | CoRThunk face ->
      traverse_face face >>= fun face' ->
      M.ret @@ CoRThunk face'

    | Box info ->
      traverse_tm info.r >>= fun r ->
      traverse_tm info.r' >>= fun r' ->
      traverse_tm info.cap >>= fun cap ->
      traverse_list traverse_face info.sys >>= fun sys ->
      M.ret @@ Box {r; r'; cap; sys}

    | LblTy info ->
      traverse_list (traverse_pair traverse_tm traverse_tm) info.args >>= fun args ->
      traverse_tm info.ty >>= fun ty ->
      M.ret @@ LblTy {info with args; ty}

    | LblRet t ->
      traverse_tm t >>= fun t' ->
      M.ret @@ LblRet t'

    | Let (cmd, bnd) ->
      traverse_cmd cmd >>= fun cmd' ->
      traverse_bnd traverse_tm bnd >>= fun bnd' ->
      M.ret @@ Let (cmd', bnd')

    | Up cmd ->
      traverse_cmd cmd >>= fun cmd' ->
      M.ret @@ Up cmd'

  and traverse_cmd (hd, sp) =
    traverse_head hd >>= fun (hd', sp') ->
    begin
      match hd' with
      | Meta _ ->
        A.under_meta @@ traverse_spine sp
      | _ ->
        traverse_spine sp
    end >>= fun sp'' ->
    M.ret (hd', sp' <.> sp'')

  and traverse_spine sp =
    traverse_bwd traverse_frame sp

  and traverse_head =
    function
    | Ix (ix, twin) ->
      A.bvar ~ih:traverse_cmd ~ix ~twin

    | Var {name; twin; ushift} ->
      (* TODO *)
      A.fvar ~name ~twin ~ushift

    | Meta {name; ushift} ->
      A.meta ~name ~ushift

    | Down info ->
      traverse_tm info.ty >>= fun ty ->
      traverse_tm info.tm >>= fun tm ->
      M.ret (Down {ty; tm}, Emp)

    | Coe info ->
      traverse_tm info.r >>= fun r ->
      traverse_tm info.r' >>= fun r' ->
      traverse_bnd traverse_tm info.ty >>= fun ty ->
      traverse_tm info.tm >>= fun tm ->
      let coe = Coe {r; r'; ty; tm} in
      M.ret (coe, Emp)

    | HCom info ->
      traverse_tm info.r >>= fun r ->
      traverse_tm info.r' >>= fun r' ->
      traverse_tm info.ty >>= fun ty ->
      traverse_tm info.cap >>= fun cap ->
      traverse_list traverse_bface info.sys >>= fun sys ->
      let hcom = HCom {r; r'; ty; cap; sys} in
      M.ret (hcom, Emp)

    | GHCom info ->
      traverse_tm info.r >>= fun r ->
      traverse_tm info.r' >>= fun r' ->
      traverse_tm info.ty >>= fun ty ->
      traverse_tm info.cap >>= fun cap ->
      traverse_list traverse_bface info.sys >>= fun sys ->
      let hcom = GHCom {r; r'; ty; cap; sys} in
      M.ret (hcom, Emp)

    | Com info ->
      traverse_tm info.r >>= fun r ->
      traverse_tm info.r' >>= fun r' ->
      traverse_bnd traverse_tm info.ty >>= fun ty ->
      traverse_tm info.cap >>= fun cap ->
      traverse_list traverse_bface info.sys >>= fun sys ->
      let com = Com {r; r'; ty; cap; sys} in
      M.ret (com, Emp)

    | GCom info ->
      traverse_tm info.r >>= fun r ->
      traverse_tm info.r' >>= fun r' ->
      traverse_bnd traverse_tm info.ty >>= fun ty ->
      traverse_tm info.cap >>= fun cap ->
      traverse_list traverse_bface info.sys >>= fun sys ->
      let com = GCom {r; r'; ty; cap; sys} in
      M.ret (com, Emp)

  and traverse_bnd : 'a. ('a -> 'b M.m) -> 'a bnd -> 'b bnd M.m =
    fun f (B (nm, tm)) ->
      A.push_bindings 1
        begin
          f tm
        end >>= fun tm' ->
      M.ret @@ B (nm, tm')

  and traverse_nbnd : 'a 'b. ('a -> 'b M.m) -> 'a nbnd -> 'b nbnd M.m =
    fun f (NB (nms, tm)) ->
      A.push_bindings (Bwd.length nms)
        begin
          f tm
        end >>= fun tm' ->
      M.ret @@ NB (nms, tm')

  and traverse_bface (r, r', obnd) =
    traverse_tm r >>= fun s ->
    traverse_tm r' >>= fun s' ->
    traverse_opt (traverse_bnd traverse_tm) obnd >>= fun obnd' ->
    M.ret (s, s', obnd')

  and traverse_face (r, r', otm) =
    traverse_tm r >>= fun s ->
    traverse_tm r' >>= fun s' ->
    traverse_opt traverse_tm otm >>= fun otm' ->
    M.ret (s, s', otm')

  and traverse_pair : 'a 'b 'c 'd. ('a -> 'c M.m) -> ('b -> 'd M.m) -> 'a * 'b -> ('c * 'd) M.m =
    fun f g (a, b) ->
      f a >>= fun c ->
      g b >>= fun d ->
      M.ret (c, d)

  and traverse_opt : 'a 'b. ('a -> 'b M.m) -> 'a option -> 'b option M.m =
    fun f ->
      function
      | None ->
        M.ret None
      | Some a ->
        f a >>= fun a' ->
        M.ret @@ Some a'

  and traverse_list : 'a 'b. ('a -> 'b M.m) -> 'a list -> 'b list M.m =
    fun f ->
      function
      | [] -> M.ret []
      | x :: xs ->
        f x >>= fun x' ->
        traverse_list f xs >>= fun xs' ->
        M.ret @@ x' :: xs'

  and traverse_bwd : 'a 'b. ('a -> 'b M.m) -> 'a bwd -> 'b bwd M.m =
    fun f ->
      function
      | Emp -> M.ret Emp
      | Snoc (xs, x) ->
        traverse_bwd f xs >>= fun xs' ->
        f x >>= fun x' ->
        M.ret @@ Snoc (xs', x')


  and traverse_frame =
    function
    | (Car | Cdr | LblCall | CoRForce as frm) ->
      M.ret frm

    | FunApp t ->
      traverse_tm t >>= fun t' ->
      M.ret @@ FunApp t'

    | ExtApp ts ->
      traverse_bwd traverse_tm ts >>= fun ts' ->
      M.ret @@ ExtApp ts'

    | If info ->
      traverse_bnd traverse_tm info.mot >>= fun mot ->
      traverse_tm info.tcase >>= fun tcase ->
      traverse_tm info.fcase >>= fun fcase ->
      M.ret @@ If {mot; tcase; fcase}

    | NatRec info ->
      traverse_bnd traverse_tm info.mot >>= fun mot ->
      traverse_tm info.zcase >>= fun zcase ->
      traverse_nbnd traverse_tm info.scase >>= fun scase ->
      M.ret @@ NatRec {mot; zcase; scase}

    | IntRec info ->
      traverse_bnd traverse_tm info.mot >>= fun mot ->
      traverse_bnd traverse_tm info.pcase >>= fun pcase ->
      traverse_bnd traverse_tm info.ncase >>= fun ncase ->
      M.ret @@ IntRec {mot; pcase; ncase}

    | S1Rec info ->
      traverse_bnd traverse_tm info.mot >>= fun mot ->
      traverse_tm info.bcase >>= fun bcase ->
      traverse_bnd traverse_tm info.lcase >>= fun lcase ->
      M.ret @@ S1Rec {mot; bcase; lcase}

    | VProj info ->
      traverse_tm info.r >>= fun r ->
      traverse_tm info.ty0 >>= fun ty0 ->
      traverse_tm info.ty1 >>= fun ty1 ->
      traverse_tm info.equiv >>= fun equiv ->
      M.ret @@ VProj {r; ty0; ty1; equiv}

    | Cap info ->
      traverse_tm info.r >>= fun r ->
      traverse_tm info.r' >>= fun r' ->
      traverse_tm info.ty >>= fun ty ->
      traverse_list traverse_bface info.sys >>= fun sys ->
      M.ret @@ Cap {r; r'; ty; sys}
end




module OpenVarAlg :
sig
  include Alg
  val run : int -> (twin -> tm cmd) -> 'a M.m -> 'a
end =
struct
  type state = { cmd : twin -> tm cmd; depth: int}

  module M = ReaderMonad.M (struct type t = state end)
  module Notation = Monad.Notation (M)
  open Notation

  let run k cmd =
    M.run {cmd; depth = k}

  let push_bindings n =
    M.local @@ fun st ->
    {st with depth = st.depth + n}

  let under_meta m = m

  let bvar ~ih ~ix ~twin =
    M.get >>= fun st ->
    if ix = st.depth then
      M.ret @@ st.cmd twin
    else
      M.ret (Ix (ix, twin), Emp)

  let fvar ~name ~twin ~ushift =
    M.ret (Var {name; twin; ushift}, Emp)

  let meta ~name ~ushift =
    M.ret (Meta {name; ushift}, Emp)
end

module SubstAlg :
sig
  include Alg
  val run : tm cmd subst -> 'a M.m -> 'a
end =
struct
  type state = tm cmd subst

  module M = ReaderMonad.M (struct type t = state end)
  module Notation = Monad.Notation (M)
  open Notation

  let run = M.run

  let push_bindings k =
    M.local @@ fun sub ->
    Lift (k, sub)

  let under_meta m = m

  let rec bvar ~ih ~ix ~twin =
    M.get >>= fun sub ->
    match sub, ix with
    | Shift n, _ ->
      M.ret (Ix (ix + n, twin), Emp)
    | Dot (cmd, _), 0 ->
      M.ret cmd
    | Dot (_, sub), _ ->
      M.local (fun _ -> sub) @@
      bvar ~ih ~ix:(ix - 1) ~twin
    | Lift (0, sub), _ ->
      M.local (fun _ -> sub) @@
      bvar ~ih ~ix:ix ~twin

    | Lift (n, sub), 0 ->
      M.ret (Ix (ix, twin), Emp)

    | Lift (n, sub), _ ->
      begin
        M.local (fun _ -> sub) @@
        bvar ~ih ~ix:(ix - n) ~twin
      end >>= fun cmd ->
      M.local (fun _ -> Shift n) @@
      ih cmd

  let fvar ~name ~twin ~ushift =
    M.ret (Var {name; twin; ushift}, Emp)

  let meta ~name ~ushift =
    M.ret (Meta {name; ushift}, Emp)
end


let open_var k cmd tm =
  let module T = Traverse (OpenVarAlg) in
  OpenVarAlg.run k cmd @@ T.traverse_tm tm

let subst sub tm =
  let module T = Traverse (SubstAlg) in
  SubstAlg.run sub @@ T.traverse_tm  tm



let make con =
  match con with
  | Up (Ix (ix, _), _) when ix < 0 ->
    raise @@ E (InvalidDeBruijnIndex ix)
  | _ -> Tm con

let unleash (Tm con) = con

module CloseVarAlg :
sig
  include Alg
  val run : twin:(twin -> twin) -> name:Name.t -> ix:int -> 'a M.m -> 'a
end =
struct
  type state = {twin : twin -> twin; name : Name.t; ix : int}
  module M = ReaderMonad.M (struct type t = state end)
  module Notation = Monad.Notation (M)
  open Notation

  let run ~twin ~name ~ix =
    M.run {twin; name; ix}

  let under_meta m = m

  let push_bindings n =
    M.local @@ fun st ->
    {st with ix = n + st.ix}

  let bvar ~ih ~ix ~twin =
    M.ret (Ix (ix, twin), Emp)

  let fvar ~name ~twin ~ushift =
    M.get >>= fun st ->
    M.ret @@
    if name = st.name then
      Ix (st.ix, st.twin twin), Emp
    else
      Var {name; twin; ushift}, Emp


  let meta ~name ~ushift =
    M.ret (Meta {name; ushift}, Emp)
end

let close_var a ?twin:(twin = fun _ -> `Only) k tm =
  let module T = Traverse (CloseVarAlg) in
  CloseVarAlg.run ~twin ~name:a ~ix:k @@ T.traverse_tm tm


let unbind (B (nm, t)) =
  let x = Name.named nm in
  x, open_var 0 (fun _ -> var x) t

let unbind_with cmd (B (_, t)) =
  open_var 0 (fun _ -> cmd) t

let unbindn (NB (nms, t)) =
  let rec go k nms xs t =
    match nms with
    | Emp -> Bwd.rev xs, t
    | Snoc (nms, nm) ->
      let x = Name.named nm in
      go (k + 1) nms (xs #< x) @@ open_var k (fun _ -> var x) t
  in
  go 0 nms Emp t

let map_tm_face f (r, r', otm) =
  f r, f r', Option.map f otm

let map_tm_sys f =
  List.map @@ map_tm_face f

let unbind_ext (NB (nms, (ty, sys))) =
  let rec go k nms xs ty sys =
    match nms with
    | Emp -> Bwd.rev xs, ty, sys
    | Snoc (nms, nm)  ->
      let x = Name.named nm in
      go (k + 1) nms (xs #< x) (open_var k (fun _ -> var x) ty) (map_tm_sys (open_var k (fun _ -> var x)) sys)
  in
  go 0 nms Emp ty sys

let unbind_ext_with xs ebnd =
  let NB (nms, (ty, sys)) = ebnd in
  let rec go k xs ty sys =
    match xs with
    | [] -> ty, sys
    | x :: xs ->
      go (k + 1) xs (open_var k (fun _ -> var x) ty) (map_tm_sys (open_var k (fun _ -> var x)) sys)
  in
  if Bwd.length nms = List.length xs then
    go 0 xs ty sys
  else
    let err = UnbindExtLengthMismatch (xs, ebnd) in
    raise @@ E err


let bind x tx =
  B (Name.name x, close_var x 0 tx)

let rec bindn xs txs =
  let rec go k xs txs =
    match xs with
    | Emp -> txs
    | Snoc (xs, x) ->
      go (k + 1) xs @@ close_var x k txs
  in
  NB (Bwd.map Name.name xs, go 0 xs txs)

let rec bind_ext xs tyxs sysxs =
  let rec go k xs tyxs sysxs =
    match xs with
    | Emp -> tyxs, sysxs
    | Snoc (xs, x) ->
      go (k + 1) xs (close_var x k tyxs) (map_tm_sys (close_var x k) sysxs)
  in
  NB (Bwd.map Name.name xs, go 0 xs tyxs sysxs)

let rec pp env fmt =

  let rec go env mode fmt (Tm t) =
    match t with
    | Pi (dom, B (nm, cod)) ->
      let x, env' = Pretty.Env.bind nm env in
      if mode = `Pi then
        Format.fprintf fmt "[%a : %a]@ %a" Uuseg_string.pp_utf_8 x (pp env) dom (go env' `Pi) cod
      else
        Format.fprintf fmt "@[<hv1>(%a @[<hv>[%a : %a]@ %a@])@]" Uuseg_string.pp_utf_8 "→" Uuseg_string.pp_utf_8 x (pp env) dom (go env' `Pi) cod

    | Sg (dom, B (nm, cod)) ->
      let x, env' = Pretty.Env.bind nm env in
      if mode = `Sg then
        Format.fprintf fmt "[%a : %a]@ %a" Uuseg_string.pp_utf_8 x (pp env) dom (go env' `Sg) cod
      else
        Format.fprintf fmt "@[<hv1>(%a @[<hv>[%a : %a]@ %a@])@]" Uuseg_string.pp_utf_8 "×" Uuseg_string.pp_utf_8 x (pp env) dom (go env' `Sg) cod

    | Ext (NB (nms, (cod, sys))) ->
      let xs, env' = Pretty.Env.bindn (Bwd.to_list nms) env in
      begin
        match sys with
        | [] ->
          Format.fprintf fmt "@[<hv1>(# <%a>@ %a)@]" pp_strings xs (pp env') cod
        | _ ->
          Format.fprintf fmt "@[<hv1>(# @[<hv1><%a>@ %a@ @[<hv>%a@]@])@]" pp_strings xs (pp env') cod (pp_sys env') sys
      end


    | Rst {ty; sys}  ->
      begin
        match sys with
        | [] ->
          Format.fprintf fmt "%a" (pp env) ty
        | _ ->
          Format.fprintf fmt "@[<hv1>(%a@ @[<hv>%a@])@]" (pp env) ty (pp_sys env) sys
      end

    | CoR face ->
      Format.fprintf fmt "@[<hv1>(=>@ %a)@]" (pp_face env) face

    | V info ->
      Format.fprintf fmt "@[<hv1>(V %a@ %a@ %a@ %a)@]" (pp env) info.r (pp env) info.ty0 (pp env) info.ty1 (pp env) info.equiv

    | VIn info ->
      Format.fprintf fmt "@[<hv1>(Vin %a@ %a@ %a)@]" (pp env) info.r (pp env) info.tm0 (pp env) info.tm1

    | Lam (B (nm, tm)) ->
      let x, env' = Pretty.Env.bind nm env in
      if mode = `Lam then
        Format.fprintf fmt "[%a]@ %a" Uuseg_string.pp_utf_8 x (go env' `Lam) tm
      else
        Format.fprintf fmt "@[<1>(λ [%a]@ %a)@]" Uuseg_string.pp_utf_8 x (go env' `Lam) tm

    | ExtLam (NB (nms, tm)) ->
      let xs, env' = Pretty.Env.bindn (Bwd.to_list nms) env in
      if mode = `Lam then
        Format.fprintf fmt "<%a>@ %a" pp_strings xs (go env' `Lam) tm
      else
        Format.fprintf fmt "@[<hv1>(λ <%a>@ %a)@]" pp_strings xs (go env' `Lam) tm

    | CoRThunk face ->
      pp_face env fmt face

    | Bool ->
      Format.fprintf fmt "bool"

    | Tt ->
      Format.fprintf fmt "tt"

    | Ff ->
      Format.fprintf fmt "ff"

    | Nat ->
      Format.fprintf fmt "nat"

    | Zero ->
      Format.fprintf fmt "zero"

    | Suc n ->
      Format.fprintf fmt "@[<hv1> (suc %a)@]" (go env `Suc) n

    | Int ->
      Format.fprintf fmt "int"

    | Pos n ->
      Format.fprintf fmt "@[<hv1> (pos %a)@]" (go env `Pos) n

    | NegSuc n ->
      Format.fprintf fmt "@[<hv1> (negsuc %a)@]" (go env `NegSuc) n

    | Dim0 ->
      Format.fprintf fmt "0"

    | Dim1 ->
      Format.fprintf fmt "1"

    | S1 ->
      Format.fprintf fmt "S1"

    | Base ->
      Format.fprintf fmt "base"

    | Loop r ->
      Format.fprintf fmt "(loop %a)" (pp env) r

    | Univ {kind; lvl} ->
      Format.fprintf fmt "(U %a %a)" Kind.pp kind Lvl.pp lvl

    | FCom {r; r'; cap; sys} ->
      Format.fprintf fmt "@[<hv1>(fcom %a %a@ %a@ @[%a@])@]" (pp env) r (pp env) r' (pp env) cap (pp_bsys env) sys

    | LblTy {lbl; args; ty} ->
      begin
        match args with
        | [] ->
          Format.fprintf fmt "@[<hv1>{%a : %a}@]"
            Uuseg_string.pp_utf_8 lbl
            (pp env) ty
        | _ ->
          Format.fprintf fmt "@[<hv1>{%a %a : %a}@]"
            Uuseg_string.pp_utf_8 lbl
            (pp_lbl_args env) args
            (pp env) ty
      end

    | LblRet t ->
      Format.fprintf fmt "@[<hv1>(ret@ %a)@]"
        (pp env) t

    | Cons (tm0, tm1) ->
      Format.fprintf fmt "@[<hv1>(cons@ %a@ %a)@]" (pp env) tm0 (pp env) tm1

    | Box {r; r'; cap; sys} ->
      Format.fprintf fmt "@[<hv1>(box %a %a@ %a@ @[<hv>%a@])@]" (pp env) r (pp env) r' (pp env) cap (pp_sys env) sys

    | Let (cmd, B (nm, t)) ->
      let x, env' = Pretty.Env.bind nm env in
      Format.fprintf fmt "@[<hv1>(let@ @[<hv1>[%a %a]@]@ %a)@]" Uuseg_string.pp_utf_8 x (pp_cmd env) cmd (pp env') t

    | Up cmd ->
      pp_cmd env fmt cmd

  in
  go env `Start fmt

and pp_head env fmt =
  function
  | Coe {r; r'; ty = B (nm, ty); tm} ->
    let x, env' = Pretty.Env.bind nm env in
    Format.fprintf fmt "@[<hv1>(coe %a %a@ <%a> %a@ %a)@]" (pp env) r (pp env) r' Uuseg_string.pp_utf_8 x (pp env') ty (pp env) tm

  | HCom {r; r'; ty; cap; sys} ->
    Format.fprintf fmt "@[<hv1>(hcom %a %a@ %a@ %a@ @[%a@])@]" (pp env) r (pp env) r' (pp env) ty (pp env) cap (pp_bsys env) sys

  | Com {r; r'; ty = B (nm, ty); cap; sys} ->
    let x, env' = Pretty.Env.bind nm env in
    Format.fprintf fmt "@[<hv1>(com %a %a@ [%a] %a@ %a@ @[%a@])@]" (pp env) r (pp env) r' Uuseg_string.pp_utf_8 x (pp env') ty (pp env) cap (pp_bsys env) sys

  | GHCom {r; r'; ty; cap; sys} ->
    Format.fprintf fmt "@[<hv1>(ghcom %a %a@ %a@ %a@ @[%a@])@]" (pp env) r (pp env) r' (pp env) ty (pp env) cap (pp_bsys env) sys

  | GCom {r; r'; ty = B (nm, ty); cap; sys} ->
    let x, env' = Pretty.Env.bind nm env in
    Format.fprintf fmt "@[<hv1>(gcom %a %a@ [%a] %a@ %a@ @[%a@])@]" (pp env) r (pp env) r' Uuseg_string.pp_utf_8 x (pp env') ty (pp env) cap (pp_bsys env) sys

  | Ix (ix, _tw) ->
    Uuseg_string.pp_utf_8 fmt @@
    Pretty.Env.var ix env

  | Var {name; ushift} ->
    Name.pp fmt name;
    if ushift > 0 then Format.fprintf fmt "^%i" ushift else ()

  | Meta {name; ushift} ->
    Format.fprintf fmt "?%a^%i"
      Name.pp name
      ushift

  | Down {ty; tm} ->
    Format.fprintf fmt "@[<hv1>(%a@ %a@ %a)@]" Uuseg_string.pp_utf_8 "▷" (pp env) ty (pp env) tm

and pp_cmd env fmt (hd, sp) =
  let rec go mode fmt sp =
    match sp with
    | Emp -> pp_head env fmt hd
    | Snoc (sp, f)->
      match f with
      | Car ->
        Format.fprintf fmt "@[<hv1>(car@ %a)@]" (go `Car) sp
      | Cdr ->
        Format.fprintf fmt "@[<hv1>(cdr@ %a)@]" (go `Car) sp
      | FunApp t ->
        if mode = `FunApp then
          Format.fprintf fmt "%a@ %a" (go `FunApp) sp (pp env) t
        else
          Format.fprintf fmt "@[<hv1>(%a@ %a)@]" (go `FunApp) sp (pp env) t
      | ExtApp ts ->
        Format.fprintf fmt "@[<hv1>(%s %a@ %a)@]" "@" (go `ExtApp) sp (pp_terms env) ts
      | If {mot = B (nm, mot); tcase; fcase} ->
        let x, env' = Pretty.Env.bind nm env in
        Format.fprintf fmt "@[<hv1>(if@ [%a] %a@ %a@ %a@ %a)@]" Uuseg_string.pp_utf_8 x (pp env') mot (go `If) sp (pp env) tcase (pp env) fcase
      | NatRec {mot = B (nm, mot); zcase; scase = NB (nms_scase, scase)} ->
        let x_mot, env'_mot = Pretty.Env.bind nm env in
        let xs_scase, env'_scase = Pretty.Env.bindn (Bwd.to_list nms_scase) env in
        Format.fprintf fmt "@[<hv1>(nat-rec@ [%a] %a@ %a@ %a@ [%a] %a)@]" Uuseg_string.pp_utf_8 x_mot (pp env'_mot) mot (go `NatRec) sp (pp env) zcase pp_strings xs_scase (pp env'_scase) scase
      | IntRec {mot = B (nm, mot); pcase = B (nm_pcase, pcase); ncase = B (nm_ncase, ncase)} ->
        let x_mot, env'_mot = Pretty.Env.bind nm env in
        let x_pcase, env'_pcase = Pretty.Env.bind nm_pcase env in
        let x_ncase, env'_ncase = Pretty.Env.bind nm_ncase env in
        Format.fprintf fmt "@[<hv1>(int-rec@ [%a] %a@ %a@ [%a] %a@ [%a] %a)@]" Uuseg_string.pp_utf_8 x_mot (pp env'_mot) mot (go `IntRec) sp Uuseg_string.pp_utf_8 x_pcase (pp env'_pcase) pcase Uuseg_string.pp_utf_8 x_ncase (pp env'_ncase) ncase
      | S1Rec {mot = B (nm_mot, mot); bcase; lcase = B (nm_lcase, lcase)} ->
        let x_mot, env_mot = Pretty.Env.bind nm_mot env in
        let x_lcase, env_lcase = Pretty.Env.bind nm_lcase env in
        Format.fprintf fmt "@[<hv1>(S1rec@ [%a] %a@ %a %a [%a] %a)@]" Uuseg_string.pp_utf_8 x_mot (pp env_mot) mot (go `S1Rec) sp (pp env) bcase Uuseg_string.pp_utf_8 x_lcase (pp env_lcase) lcase
      | VProj {r; ty0; ty1; equiv} ->
        Format.fprintf fmt "@[<hv1>(vproj %a@ %a@ %a@ %a@ %a)@]" (pp env) r (go `VProj) sp (pp env) ty0 (pp env) ty1 (pp env) equiv
      | Cap _ ->
        (* FIXME *)
        Format.fprintf fmt "@<cap>"
      | LblCall ->
        Format.fprintf fmt "@[<hv1>(call@ %a)@]" (go `Call) sp
      | CoRForce ->
        Format.fprintf fmt "@[<hv1>(force@ %a)@]" (go `Force) sp
  in
  go `Start fmt sp

and pp_spine env fmt sp =
  match sp with
  | Emp ->
    Format.fprintf fmt "[]"
  | Snoc (sp, f) ->
    Format.fprintf fmt "%a; %a"
      (pp_spine env) sp
      (pp_frame env) f

and pp_frame env fmt =
  function
  | FunApp t ->
    Format.fprintf fmt "@[<hv1>(app %a)@]" (pp env) t
  | ExtApp ts ->
    Format.fprintf fmt "@[<hv1>(ext-app %a)@]" (pp_terms env) ts
  | Car ->
    Format.fprintf fmt "car"
  | Cdr ->
    Format.fprintf fmt "cdr"
  | If _ ->
    Format.fprintf fmt "<if>"
  | NatRec _ ->
    Format.fprintf fmt "<nat-rec>"
  | IntRec _ ->
    Format.fprintf fmt "<int-rec>"
  | _ ->
    Format.fprintf fmt "<frame>"

and pp_lbl_args env fmt args =
  let pp_sep fmt () = Format.fprintf fmt " " in
  let pp_arg fmt (_, tm) = pp env fmt tm in
  Format.pp_print_list ~pp_sep pp_arg fmt args

and pp_terms env fmt ts =
  let pp_sep fmt () = Format.fprintf fmt "@ " in
  Format.pp_print_list ~pp_sep (pp env) fmt (Bwd.to_list ts)

and pp_strings fmt (xs : string list) : unit =
  let pp_sep fmt () = Format.fprintf fmt " " in
  Format.pp_print_list ~pp_sep Uuseg_string.pp_utf_8 fmt xs

and pp_sys env fmt sys =
  match sys with
  | [] ->
    ()

  | [face] ->
    pp_face env fmt face

  | face :: sys ->
    Format.fprintf fmt "%a@ %a" (pp_face env) face (pp_sys env) sys

and pp_bsys env fmt sys =
  match sys with
  | [] ->
    ()

  | [face] ->
    pp_bface env fmt face

  | face :: sys ->
    Format.fprintf fmt "%a@ %a" (pp_bface env) face (pp_bsys env) sys

and pp_face env fmt face =
  let r, r', otm = face in
  match otm with
  | None ->
    Format.fprintf fmt "@[<hv1>[%a=%a@ -]@]" (pp env) r (pp env) r'

  | Some tm ->
    Format.fprintf fmt "@[<hv1>[%a=%a@ %a]@]" (pp env) r (pp env) r' (pp env) tm

and pp_bface env fmt face =
  let r, r', obnd = face in
  match obnd with
  | None ->
    Format.fprintf fmt "@[<hv1>[%a=%a@ -]@]" (pp env) r (pp env) r'

  | Some (B (nm, tm)) ->
    let x, env' = Pretty.Env.bind nm env in
    Format.fprintf fmt "@[<hv1>[%a=%a@ <%a> %a]@]" (pp env) r (pp env) r' Uuseg_string.pp_utf_8 x (pp env') tm


let up cmd = make @@ Up cmd

let car (hd, sp) =
  hd, sp #< Car

let cdr (hd, sp) =
  hd, sp #< Cdr

let lam nm t = make @@ Lam (B (nm, t))
let ext_lam nms t = make @@ ExtLam (NB (nms, t))
let pi nm dom cod = make @@ Pi (dom, B (nm, cod))
let sg nm dom cod = make @@ Sg (dom, B (nm, cod))
let let_ nm t0 t1 = make @@ Let (t0, B (nm, t1))
let cons t0 t1 = make @@ Cons (t0, t1)
let univ ~kind ~lvl = make @@ Univ {kind; lvl}

module Macro =
struct
  let arr ty0 ty1 =
    pi None ty0 @@
    subst (Shift 1) ty1

  let times ty0 ty1 =
    sg None ty0 @@
    subst (Shift 1) ty1

  let path ty tm0 tm1 =
    let ty' = subst (Shift 1) ty in
    let face0 = up (ix 0), make Dim0, Some (subst (Shift 1) tm0) in
    let face1 = up (ix 0), make Dim1, Some (subst (Shift 1) tm1) in
    let sys = [face0; face1] in
    make @@ Ext (NB (Emp #< None, (ty', sys)))

  let fiber ~ty0 ~ty1 ~f ~x =
    sg (Some "ix") ty0 @@
    let app =
      Down {tm = subst (Shift 1) f; ty = arr ty0 ty1},
      (Emp #< (FunApp (up (ix 0))))
    in
    path
      (subst (Shift 1) ty1)
      (up app)
      (subst (Shift 1) x)

  let proj2 = Shift 2

  let is_contr ty =
    sg (Some "center") ty @@
    pi (Some "other") (subst (Shift 1) ty) @@
    path
      (subst proj2 ty)
      (up @@ ix 0)
      (up @@ ix 1)

  let equiv ty0 ty1 =
    sg (Some "fun") (arr ty0 ty1) @@
    pi (Some "el") (subst (Shift 1) ty1) @@
    is_contr @@
    fiber
      ~ty0:(subst proj2 ty0)
      ~ty1:(subst proj2 ty1)
      ~f:(up @@ ix 1)
      ~x:(up @@ ix 0)
end


module OccursAlg :
sig
  include Alg
  val run : Occurs.flavor -> 'a M.m -> 'a * Occurs.Set.t
end =
struct
  type set = Occurs.Set.t
  type state = {fl : Occurs.flavor; vars : set; srigid: bool}

  module M = StateMonad.M (struct type t = state end)
  module Notation = Monad.Notation (M)
  open Notation

  let run fl m =
    let init = {fl; vars = Occurs.Set.empty; srigid = true} in
    let a, st = M.run init m in
    a, st.vars

  let insert x =
    M.get >>= fun st ->
    M.set @@ {st with vars = Occurs.Set.add x st.vars}

  let push_bindings _ m =
    m

  let under_meta m =
    M.get >>= fun st0 ->
    M.set {st0 with srigid = false} >>
    m >>= fun a ->
    M.get >>= fun st1 ->
    M.set {st1 with srigid = st0.srigid} >>
    M.ret a

  let bvar ~ih ~ix ~twin =
    M.ret (Ix (ix, twin), Emp)

  let fvar ~name ~twin ~ushift =
    M.get >>= fun st ->
    begin
      if st.fl = `Vars || (st.fl = `RigVars && st.srigid) then
        insert name
      else
        M.ret ()
    end >>
    M.ret (Var {name; twin; ushift}, Emp)

  let meta ~name ~ushift =
    M.get >>= fun st ->
    begin
      if st.fl = `Metas then
        insert name
      else
        M.ret ()
    end >>
    M.ret (Meta {name; ushift}, Emp)
end




let free fl tm =
  let module T = Traverse (OccursAlg) in
  let _, xs = OccursAlg.run fl @@ T.traverse_tm tm in
  xs

module Sp =
struct
  type t = tm spine
  let free fl sp =
    let module T = Traverse (OccursAlg) in
    let _, xs = OccursAlg.run fl @@ T.traverse_spine sp in
    xs
end

let map_bnd (f : tm -> tm) (bnd : tm bnd) : tm bnd =
  let x, tx = unbind bnd in
  bind x @@ f tx

(* TODO: clean up *)
let map_nbnd (f : tm -> tm) (nbnd : tm nbnd) : tm nbnd =
  let xs, txs = unbindn nbnd in
  bindn xs @@ f txs


let map_comp_face f (r, r', obnd) =
  f r, f r', Option.map (map_bnd f) obnd

let map_comp_sys f =
  List.map @@ map_comp_face f

let map_head f =
  function
  | Var info -> Var info
  | Meta a -> Meta a
  | Ix (i, tw) -> Ix (i, tw)
  | Down info ->
    let ty = f info.ty in
    let tm = f info.tm in
    Down {ty; tm}
  | Coe info ->
    let r = f info.r in
    let r' = f info.r' in
    let ty = map_bnd f info.ty in
    let tm = f info.tm in
    Coe {r; r'; ty; tm}
  | HCom info ->
    let r = f info.r in
    let r' = f info.r' in
    let ty = f info.ty in
    let cap = f info.cap in
    let sys = map_comp_sys f info.sys in
    HCom {r; r'; ty; cap; sys}
  | Com info ->
    let r = f info.r in
    let r' = f info.r' in
    let ty = map_bnd f info.ty in
    let cap = f info.cap in
    let sys = map_comp_sys f info.sys in
    Com {r; r'; ty; cap; sys}
  | GHCom info ->
    let r = f info.r in
    let r' = f info.r' in
    let ty = f info.ty in
    let cap = f info.cap in
    let sys = map_comp_sys f info.sys in
    GHCom {r; r'; ty; cap; sys}
  | GCom info ->
    let r = f info.r in
    let r' = f info.r' in
    let ty = map_bnd f info.ty in
    let cap = f info.cap in
    let sys = map_comp_sys f info.sys in
    GCom {r; r'; ty; cap; sys}

let map_frame f =
  function
  | (Car | Cdr | LblCall | CoRForce) as frm ->
    frm
  | FunApp t ->
    FunApp (f t)
  | ExtApp ts ->
    ExtApp (Bwd.map f ts)
  | If info ->
    let mot = map_bnd f info.mot in
    let tcase = f info.tcase in
    let fcase = f info.fcase in
    If {mot; tcase; fcase}
  | NatRec info ->
    let mot = map_bnd f info.mot in
    let zcase = f info.zcase in
    let scase = map_nbnd f info.scase in
    NatRec {mot; zcase; scase}
  | IntRec info ->
    let mot = map_bnd f info.mot in
    let pcase = map_bnd f info.pcase in
    let ncase = map_bnd f info.ncase in
    IntRec {mot; pcase; ncase}
  | S1Rec info ->
    let mot = map_bnd f info.mot in
    let bcase = f info.bcase in
    let lcase = map_bnd f info.lcase in
    S1Rec {mot; bcase; lcase}
  | VProj info ->
    let r = f info.r in
    let ty0 = f info.ty0 in
    let ty1 = f info.ty1 in
    let equiv = f info.equiv in
    VProj {r; ty0; ty1; equiv}
  | Cap info ->
    let r = f info.r in
    let r' = f info.r' in
    let ty = f info.ty in
    let sys = map_comp_sys f info.sys in
    Cap {r; r'; ty; sys}

let map_spine f =
  Bwd.map @@ map_frame f


(* TODO: clean up: this is catastrophically bad *)
let rec map_ext_bnd f nbnd =
  match nbnd with
  | NB (Emp, (ty, sys)) ->
    NB (Emp, (f ty, map_tm_sys f sys))
  | NB (Snoc (nms, nm), (ty, sys)) ->
    let x = Name.named nm in
    let tyx = open_var 0 (fun _ -> var x) ty in
    let sysx = map_tm_sys (open_var 0 (fun _ -> var x)) sys in
    let NB (_, (tyx', sysx')) = map_ext_bnd f (NB (nms, (tyx, sysx))) in
    NB (nms #< nm, (close_var x 0 tyx', map_tm_sys (close_var x 0) sysx'))

let map_cmd f (hd, sp) =
  map_head f hd, map_spine f sp

let map_tmf f =
  function
  | (Univ _ | Bool | Tt | Ff | Nat | Zero | Int | Dim0 | Dim1 | S1 | Base) as con ->
    con
  | Suc n -> Suc (f n)
  | Pos n -> Pos (f n)
  | NegSuc n -> NegSuc (f n)
  | Loop r -> Loop (f r)
  | Cons (t0, t1) ->
    Cons (f t0, f t1)
  | LblRet t ->
    LblRet (f t)
  | FCom info ->
    let r = f info.r in
    let r' = f info.r' in
    let cap = f info.cap in
    let sys = map_comp_sys f info.sys in
    FCom {r; r'; cap; sys}
  | Pi (dom, cod) ->
    Pi (f dom, map_bnd f cod)
  | Sg (dom, cod) ->
    Sg (f dom, map_bnd f cod)
  | Ext ebnd ->
    Ext (map_ext_bnd f ebnd)
  | Rst {ty; sys} ->
    Rst {ty = f ty; sys = map_tm_sys f sys}
  | CoR face ->
    CoR (map_tm_face f face)
  | V info ->
    let r = f info.r in
    let ty0 = f info.ty0 in
    let ty1 = f info.ty1 in
    let equiv = f info.equiv in
    V {r; ty0; ty1; equiv}
  | VIn info ->
    let r = f info.r in
    let tm0 = f info.tm0 in
    let tm1 = f info.tm1 in
    VIn {r; tm0; tm1}
  | Lam bnd ->
    Lam (map_bnd f bnd)
  | ExtLam nbnd ->
    ExtLam (map_nbnd f nbnd)
  | CoRThunk face ->
    CoRThunk (map_tm_face f face)
  | Box info ->
    let r = f info.r in
    let r' = f info.r' in
    let cap = f info.cap in
    let sys = map_tm_sys f info.sys in
    Box {r; r'; cap; sys}
  | LblTy info ->
    let ty = f info.ty in
    let args = List.map (fun (t0, t1) -> f t0, f t1) info.args in
    LblTy {info with ty; args}
  | Up cmd ->
    Up (map_cmd f cmd)
  | Let (cmd, bnd) ->
    Let (map_cmd f cmd, map_bnd f bnd)



let rec opt_traverse f xs =
  match xs with
  | [] -> Some []
  | x::xs ->
    match f x with
    | Some y -> Option.map (fun ys -> y :: ys) @@ opt_traverse f xs
    | None -> None


let as_plain_var t =
  match unleash t with
  | Up (Var {name; _}, Emp) ->
    Some name
  | _ ->
    None

(* A very crappy eta contraction function. It's horrific that this is actually a thing that we do! *)
let rec eta_contract t =
  match unleash t with
  | Lam bnd ->
    let y, tmy = unbind bnd in
    let tm'y = eta_contract tmy in
    begin
      match unleash tm'y with
      | Up (hd, Snoc (sp, FunApp arg)) ->
        begin
          match as_plain_var arg with
          | Some y'
            when
              y = y'
              && not @@ Occurs.Set.mem y @@ Sp.free `Vars sp
            ->
            up (hd, sp)
          | _ ->
            make @@ Lam (bind y tm'y)
        end
      | _ ->
        make @@ Lam (bind y tm'y)
    end

  | ExtLam nbnd ->
    let ys, tmys = unbindn nbnd in
    let tm'ys = eta_contract tmys in
    begin
      match unleash tm'ys with
      | Up (hd, Snoc (sp, ExtApp args)) ->
        begin
          match opt_traverse as_plain_var @@ Bwd.to_list args with
          | Some y's
            when Bwd.to_list ys = y's
            (* TODO: && not @@ Occurs.Set.mem 'ys' @@ Tm.Sp.free `Vars sp *)
            ->
            up (hd, sp)
          | _ ->
            make @@ ExtLam (bindn ys tm'ys)
        end
      | _ ->
        make @@ ExtLam (bindn ys tm'ys)
    end

  | Cons (tm0, tm1) ->
    let tm0' = eta_contract tm0 in
    let tm1' = eta_contract tm1 in
    begin
      match unleash tm0', unleash tm1' with
      | Up (hd0, Snoc (sp0, Car)), Up (hd1, Snoc (sp1, Cdr))
        when
          hd0 = hd1 && sp0 = sp1
        ->
        up (hd0, sp0)

      | _ ->
        make @@ Cons (tm0', tm1')
    end

  | con ->
    make @@ map_tmf eta_contract con


let rec shift_univ k tm =
  match unleash tm with
  | Univ {lvl; kind} ->
    make @@ Univ {lvl = Lvl.shift k lvl; kind}
  | Up (Var info, sp) ->
    let hd' = Var {info with ushift = info.ushift + k} in
    let sp' = map_spine (shift_univ k) sp in
    make @@ Up (hd', sp')
  | Up (Meta {name; ushift}, sp) ->
    let hd' = Meta {name; ushift = ushift + k} in
    let sp' = map_spine (shift_univ k) sp in
    make @@ Up (hd', sp')
  | tmf ->
    Tm (map_tmf (shift_univ k) tmf)

let pp0 fmt tm = pp Pretty.Env.emp fmt @@ eta_contract tm

module Error =
struct
  type t = error
  exception E = E

  let pp fmt =
    function
    | InvalidDeBruijnIndex i ->
      Format.fprintf fmt
        "Tried to construct term with negative de bruijn index %i." i
    | UnbindExtLengthMismatch (xs, ebnd) ->
      Format.fprintf fmt
        "Tried to unbind extension type binder with incorrect number of variables."

  let _ =
    PpExn.install_printer @@ fun fmt ->
    function
    | E err ->
      pp fmt err
    | _ ->
      raise PpExn.Unrecognized

end

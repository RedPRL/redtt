open Dev
open RedBasis
open Bwd open BwdNotation

type cx_l = entry bwd
type cx_r = entry list

type cx = cx_l * cx_r


let rec pp_cx_l fmt =
  function
  | Emp ->
    ()
  | Snoc (Emp, e) ->
    Format.fprintf fmt "@[<1>%a@]"
      pp_entry e
  | Snoc (cx, e) ->
    Format.fprintf fmt "%a;@; @[<1>%a@]"
      pp_cx_l cx
      pp_entry e

let rec pp_cx_r fmt =
  function
  | [] ->
    ()
  | e :: []->
    Format.fprintf fmt "@[<1>%a@]"
      pp_entry e
  | e :: cx ->
    Format.fprintf fmt "@[<1>%a@];@; %a"
      pp_entry e
      pp_cx_r cx

let pp_cx fmt (lcx, rcx) =
  Format.fprintf fmt "@[<1>%a@] |@ @[<1>%a@]"
    pp_cx_l lcx
    pp_cx_r rcx


module M =
struct
  type 'a m = params -> cx -> cx * 'a

  let ret a _ cx = cx, a

  let bind m k ps cx =
    let cx', a = m ps cx  in
    k a ps cx'
end

module Notation = Monad.Notation (M)
include M

open Notation

let local f m ps =
  m (f ps)

let optional m ps cx =
  try
    let cx', a = m ps cx in
    cx', Some a
  with
  | _ -> cx, None

let ask ps cx = cx, ps

let get _ cx = cx, cx

let modify f _ cx = f cx, ()

let getl = fst <@> get
let getr = snd <@> get
let modifyl f = modify @@ fun (l, r) -> f l, r
let modifyr f = modify @@ fun (l, r) -> l, f r
let setl l = modifyl @@ fun _ -> l
let setr r = modifyr @@ fun _ -> r
let pushl e = modifyl @@ fun es -> es #< e
let pushr e = modifyr @@ fun es -> e :: es

let dump_state fmt str =
  get >>= fun cx ->
  Format.fprintf fmt "%s@.%a@.@." str pp_cx cx;
  ret ()

let run (m : 'a m) : 'a  =
  let _, r = m Emp (Emp, []) in
  r

let rec pushls es =
  match es with
  | [] -> ret ()
  | e :: es ->
    pushl e >>
    pushls es

let popl =
  getl >>= function
  | Snoc (mcx, e) -> setl mcx >> ret e
  | _ -> failwith "popl: empty"



let cx_core : cx_l -> GlobalCx.t =
  let rec go es =
    match es with
    | Emp -> GlobalCx.emp
    | Snoc (es, e) ->
      match e with
      | E (x, ty, Hole) ->
        let cx = go es in
        GlobalCx.add_hole cx x ty []
      | E (x, ty, Defn t) ->
        let cx = go es in
        GlobalCx.define cx x ty t
      | Q _ ->
        go es
      | Bracket _ ->
        go es
  in
  go

let get_global_cx =
  get >>= fun (cxl, cxr) ->
  let rec go_params =
    function
    | Emp ->cx_core (cxl <>< cxr)
    | Snoc (psi, (x, P ty)) ->
      GlobalCx.add_hole (go_params psi) x ty []
    | Snoc (psi, (x, Tw (ty, _))) (* TODO *) ->
      GlobalCx.add_hole (go_params psi) x ty []
  in
  ask >>= fun psi ->
  ret @@ go_params psi


let popr_opt =
  get_global_cx >>= fun sub ->
  getr >>= function
  | e :: mcx ->
    setr mcx >>
    begin
      try
        ret @@ Some (Entry.subst sub e)
      with
      | e ->
        Format.eprintf "Failed to substitute: %s !!!!!@." (Printexc.to_string e);
        raise e
    end
  | _ ->
    ret None

let popr =
  popr_opt >>= function
  | Some e -> ret e
  | None -> failwith "popr: empty"

let go_left =
  popl >>= pushr

let go_right =
  popr >>= pushl

let go_to_top =
  get >>= fun (lcx, rcx) ->
  setl Emp >>
  setr (lcx <>> rcx)

let go_to_bottom =
  get >>= fun (lcx, rcx) ->
  setl (lcx <>< rcx) >>
  setr []

let in_scope x p =
  local @@ fun ps ->
  ps #< (x, p)

let in_scopes ps =
  local @@ fun ps' ->
  ps' <>< ps


let lookup_var x w =
  let rec go gm =
    match w, gm with
    | `Only, Snoc (gm, (y, P ty)) ->
      if x = y then M.ret ty else go gm
    | `TwinL, Snoc (gm, (y, Tw (ty0, _))) ->
      if x = y then M.ret ty0 else go gm
    | `TwinR, Snoc (gm, (y, Tw (_, ty1))) ->
      if x = y then M.ret ty1 else go gm
    | _, Snoc (gm, _) ->
      go gm
    | _ ->
      failwith "lookup_var: not found"
  in
  ask >>= go

let lookup_meta x =
  let rec look =
    function
    | Snoc (mcx, E (y, ty, _)) ->
      if x = y then M.ret ty else look mcx
    | Snoc (mcx, _) ->
      look mcx
    | Emp ->
      failwith "lookup_meta: not found"
  in
  getl >>= look


let postpone s p =
  ask >>= fun ps ->
  let wrapped =
    let rec go ps p =
      match ps with
      | Snoc (ps, (x, e)) ->
        go ps @@ All (e, Dev.bind x p)
      | Emp -> p
    in go ps p
  in
  pushr @@ Q (s, wrapped)


let active = postpone Active
let block = postpone Blocked


let typechecker : (module Typing.S) m =
  getl >>= fun entries ->
  let rec go_tele cx =
    function
    | Emp -> cx
    | Snoc (psi, (x, P ty)) ->
      let cx' = GlobalCx.add_hole cx x ~ty:ty ~sys:[] in
      go_tele cx' psi

    | Snoc (psi, (x, Tw (ty0, _ty1))) ->
      (* TODO: properly handle twin *)
      let cx' = GlobalCx.add_hole cx x ~ty:ty0 ~sys:[] in
      go_tele cx' psi
  in

  ask >>= fun psi ->
  let globals = go_tele (cx_core entries) psi  in
  let module G = struct let globals = globals end in
  let module T = Typing.M (G) in
  ret @@ (module T : Typing.S)

let check ~ty tm =
  typechecker >>= fun (module T) ->
  let lcx = T.Cx.emp in
  let vty = T.Cx.eval lcx ty in
  try
    T.check lcx vty tm;
    ret true
  with
  | _ ->
    ret false

let check_eq ~ty tm0 tm1 =
  typechecker >>= fun (module T) ->
  let lcx = T.Cx.emp in
  let vty = T.Cx.eval lcx ty in
  let el0 = T.Cx.eval lcx tm0 in
  let el1 = T.Cx.eval lcx tm1 in
  try
    T.Cx.check_eq lcx ~ty:vty el0 el1;
    ret true
  with
  | _ ->
    ret false

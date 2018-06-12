open Dev
open RedBasis
open Bwd open BwdNotation

type stamped = {stamp : float; entry : entry}
type lcx = stamped bwd
type rcx = stamped list

type env = GlobalEnv.t
type cx = {env : env; lcx : lcx; rcx : rcx; last_updated : float}


let rec pp_lcx fmt =
  function
  | Emp ->
    ()
  | Snoc (Emp, e) ->
    Format.fprintf fmt "@[<v>%a@]"
      pp_entry e.entry
  | Snoc (cx, e) ->
    Format.fprintf fmt "%a;@;@;@[<v>%a@]"
      pp_lcx cx
      pp_entry e.entry

let rec pp_rcx fmt =
  function
  | [] ->
    ()
  | e :: [] ->
    Format.fprintf fmt "@[<1>%a@]"
      pp_entry e.entry
  | e :: cx ->
    Format.fprintf fmt "@[<1>%a@];@;@;%a"
      pp_entry e.entry
      pp_rcx cx

let filter_entry filter entry =
  match filter with
  | `All -> true
  | `Constraints ->
    begin
      match entry.entry with
      | Q _ -> true
      | _ -> false
    end
  | `Unsolved ->
    begin
      match entry.entry with
      | Q _ -> true
      | E (_, _, Hole) -> true
      | E (_, _, Guess _) -> true
      | _ -> false
    end

let pp_cx filter fmt {lcx; rcx} =
  Format.fprintf fmt "@[<v>%a@]@ %a@ @[<v>%a@]"
    pp_lcx (Bwd.filter (filter_entry filter) lcx)
    Uuseg_string.pp_utf_8 "❚"
    pp_rcx (List.filter (filter_entry filter) rcx)


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


let rec fix f ps cx =
  f (fix f) ps cx

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

let getl = (fun x -> x.lcx) <@> get
let getr = (fun x -> x.rcx) <@> get
let modifyl f = modify @@ fun st -> {st with lcx = f st.lcx}
let modifyr f = modify @@ fun st -> {st with rcx = f st.rcx}
let setl l = modifyl @@ fun _ -> l
let setr r = modifyr @@ fun _ -> r

let update_env e =
  modify @@ fun st ->
  match e with
  | E (nm, ty, Hole) ->
    {st with env = GlobalEnv.ext st.env nm @@ `P {ty; sys = []}}
  | E (nm, ty, Guess _) ->
    {st with env = GlobalEnv.ext st.env nm @@ `P {ty; sys = []}}
  | E (nm, ty, Defn t) ->
    {st with env = GlobalEnv.define st.env nm ty t}
  | _ ->
    st

let get_position_left =
  getl >>= function
  | Emp -> ret 0.0
  | Snoc (_, e) -> ret e.stamp

let get_position_right =
  getr >>= function
  | [] -> ret 1000.0
  | e :: _ -> ret e.stamp

let get_position_between =
  get_position_left >>= fun l ->
  get_position_right >>= fun r ->
  ret @@ (r -. l) /. 2.0

let pushl e =
  get_position_between >>= fun stamp->
  modifyl (fun es -> es #< {stamp; entry = e}) >>
  update_env e

let pushr e =
  get_position_between >>= fun stamp->
  modifyr (fun es -> {stamp; entry = e} :: es) >>
  update_env e

let notify_stale =
  get_position_right >>= fun stamp ->
  modify @@ fun st ->
  {st with last_updated = stamp}

let run (m : 'a m) : 'a  =
  let _, r = m Emp {lcx = Emp; env = GlobalEnv.emp; rcx = []; last_updated = 10000.0} in
  r


let isolate (m : 'a m) : 'a m =
  fun ps st ->
    let st', a = m ps {st with lcx = Emp; rcx = []} in
    {env = st'.env; lcx = st.lcx <.> st'.lcx; rcx = st'.rcx @ st.rcx; last_updated = st.last_updated}, a

let rec pushls es =
  match es with
  | [] -> ret ()
  | e :: es ->
    pushl e >>
    pushls es

let dump_state fmt str filter =
  get >>= fun cx ->
  Format.fprintf fmt "@[<v2>%s@,@,@[<v>%a@]@]@.@." str (pp_cx filter) cx;
  ret ()

let popl =
  getl >>= function
  | Snoc (mcx, e) -> setl mcx >> ret e.entry
  | _ ->
    dump_state Format.err_formatter "Tried to pop-left" `All >>= fun _ ->
    failwith "popl: empty"


let get_global_env =
  get >>= fun st ->
  let rec go_params =
    function
    | Emp -> st.env
    | Snoc (psi, (_, `I)) ->
      go_params psi
    | Snoc (psi, (x, `P ty)) ->
      GlobalEnv.ext (go_params psi) x @@ `P {ty; sys = []}
    | Snoc (psi, (x, `Tw (ty0, ty1))) ->
      GlobalEnv.ext (go_params psi) x @@ `Tw ({ty = ty0; sys = []}, {ty = ty1; sys = []})
    | Snoc (psi, (_, `R (r0, r1))) ->
      GlobalEnv.restrict r0 r1 (go_params psi)
  in
  ask >>= fun psi ->
  ret @@ go_params psi


let popr_opt =
  get >>= fun st ->
  getr >>= function
  | e :: mcx ->
    setr mcx >>
    (* TODO: this is so slow that it brings everything to a halt. We need to limit when this is unleashed. *)
    (* if e.stamp > st.last_updated then
       get_global_env >>= fun sub ->
       ret @@ Some (Entry.subst sub e.entry)
       else
       begin *)
    ret @@ Some e.entry
  (* end *)
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
  get >>= fun {lcx; rcx} ->
  setl Emp >>
  setr (lcx <>> rcx)

let go_to_bottom =
  get >>= fun {lcx; rcx} ->
  setl (lcx <>< rcx) >>
  setr []

let in_scope x p =
  local @@ fun ps ->
  ps #< (x, p)

let in_scopes ps =
  local @@ fun ps' ->
  ps' <>< ps

let under_restriction r0 r1 =
  in_scope (Name.fresh ()) @@ `R (r0, r1)


let lookup_var x w =
  let rec go gm =
    match w, gm with
    | `Only, Snoc (gm, (y, `P ty)) ->
      if x = y then M.ret ty else go gm
    | `TwinL, Snoc (gm, (y, `Tw (ty0, _))) ->
      if x = y then M.ret ty0 else go gm
    | `TwinR, Snoc (gm, (y, `Tw (_, ty1))) ->
      if x = y then M.ret ty1 else go gm
    | _, Snoc (gm, _) ->
      go gm
    | _ ->
      failwith "lookup_var: not found"
  in
  ask >>= go

let lookup_meta x =
  get >>= fun {env; _} ->
  ret @@ GlobalEnv.lookup_ty env x `Only


let postpone s p =
  ask >>= fun ps ->
  let wrapped =
    let rec go ps p =
      match ps with
      | Emp ->
        p
      | Snoc (ps, (x, param)) ->
        go ps @@ All (param, Dev.bind x param p)
    in go ps p
  in
  pushr @@ Q (s, wrapped)


let active = postpone Active
let block = postpone Blocked


let typechecker : (module Typing.S) m =
  get_global_env >>= fun env ->
  let module G = struct let globals = env end in
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
  | _exn ->
    (* Format.eprintf "type error: %s@." @@ Printexc.to_string exn; *)
    ret false

let check_eq ~ty tm0 tm1 =
  if tm0 = tm1 then ret true else
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

let check_subtype ty0 ty1 =
  typechecker >>= fun (module T) ->
  let lcx = T.Cx.emp in
  let vty0 = T.Cx.eval lcx ty0 in
  let vty1 = T.Cx.eval lcx ty1 in
  try
    T.Cx.check_subtype lcx vty0 vty1;
    ret true
  with
  | _ ->
    ret false

let check_eq_dim tr0 tr1 =
  typechecker >>= fun (module T) ->
  let r0 = T.Cx.unleash_dim T.Cx.emp @@ T.Cx.eval_dim T.Cx.emp tr0 in
  let r1 = T.Cx.unleash_dim T.Cx.emp @@ T.Cx.eval_dim T.Cx.emp tr1 in
  match Dim.compare r0 r1 with
  | Same ->
    ret true
  | _ ->
    ret false

open Dev
open RedTT_Core
open RedBasis
open Bwd open BwdNotation

type lcx = entry bwd
type rcx = [`Entry of entry | `Update of Occurs.Set.t] list

module Map = Map.Make (Name)

type env = GlobalEnv.t
type per_process = {env : env; info : [`Flex | `Rigid] Map.t}
type cx = {mlenv : ML.mlenv; resenv : ResEnv.t; per_process : per_process; lcx : lcx; rcx : rcx}


let rec pp_lcx fmt =
  function
  | Emp ->
    ()
  | Snoc (Emp, e) ->
    Format.fprintf fmt "@[<v>%a@]"
      pp_entry e
  | Snoc (cx, e) ->
    Format.fprintf fmt "%a;@;@;@[<v>%a@]"
      pp_lcx cx
      pp_entry e

let rec pp_rcx fmt =
  function
  | [] ->
    ()
  | e :: [] ->
    Format.fprintf fmt "@[<1>%a@]"
      pp_entry e
  | e :: cx ->
    Format.fprintf fmt "@[<1>%a@];@;@;%a"
      pp_entry e
      pp_rcx cx

let rec rcx_entries es =
  match es with
  | [] -> []
  | `Entry e :: es -> e :: rcx_entries es
  | _ :: es -> rcx_entries es


let filter_entry filter entry =
  match filter with
  | `All -> true
  | `Constraints ->
    begin
      match entry with
      | Q _ -> true
      | _ -> false
    end
  | `Unsolved ->
    begin
      match entry with
      | Q _ -> true
      | E (_, _, Hole _) -> true
      | E (_, _, Guess _) -> true
      | _ -> false
    end

let pp_cx filter fmt {lcx; rcx} =
  Format.fprintf fmt "@[<v>%a@]@ %a@ @[<v>%a@]"
    pp_lcx (Bwd.filter (filter_entry filter) lcx)
    Uuseg_string.pp_utf_8 "❚"
    pp_rcx (List.filter (filter_entry filter) @@ rcx_entries rcx)


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

let getl = get <<@> fun x -> x.lcx
let getr = get <<@> fun x -> x.rcx
let modifyl f = modify @@ fun st -> {st with lcx = f st.lcx}
let modifyr f = modify @@ fun st -> {st with rcx = f st.rcx}
let setl l = modifyl @@ fun _ -> l
let setr r = modifyr @@ fun _ -> r

let modify_mlenv f =
  modify @@ fun st ->
  {st with mlenv = f st.mlenv}

let get_mlenv = get <<@> fun st -> st.mlenv


let assert_top_level =
  ask >>= function
  | Emp -> ret ()
  | _ -> failwith "Invalid operations outside of the top-level."

let init_per_process () =
  {env = GlobalEnv.emp (); info = Map.empty}

let get_per_process =
  assert_top_level >>
  get <<@> fun st -> st.per_process

let set_per_process per_process =
  assert_top_level >>
  modify @@ fun st -> {st with per_process}

let update_env e =
  modify @@ fun st ->
  match e with
  | E (nm, ty, Hole info) ->
    {st with per_process =
               {env = GlobalEnv.ext_meta st.per_process.env nm @@ `P ty; info = Map.add nm info st.per_process.info}}
  | E (nm, ty, Guess _) ->
    {st with per_process =
               {env = GlobalEnv.ext_meta st.per_process.env nm @@ `P ty; info = Map.add nm `Rigid st.per_process.info}}
  | E (nm, ty, Defn (visibility, `Transparent, t)) ->
    {st with
     per_process =
       {env = GlobalEnv.define st.per_process.env nm ty t;
        info = Map.add nm `Rigid st.per_process.info};
     resenv =
       begin
         match Name.name nm with
         | Some str -> ResEnv.named_metavar ~visibility str nm st.resenv
         | None -> st.resenv
       end}
  | E (nm, ty, Defn (visibility, `Opaque, _)) ->
    {st with
     per_process =
       {env = GlobalEnv.ext_meta st.per_process.env nm @@ `P ty;
        info = Map.add nm `Rigid st.per_process.info};
     resenv =
       begin
         match Name.name nm with
         | Some str -> ResEnv.named_metavar ~visibility str nm st.resenv
         | None -> st.resenv
       end}
  | _ ->
    st

let declare_datatype visibility dlbl desc =
  modify @@ fun st ->
  {st with
   per_process =
     {st.per_process with env = GlobalEnv.declare_datatype dlbl desc st.per_process.env};
   resenv = ResEnv.datatype visibility dlbl st.resenv
  }

let replace_datatype dlbl desc =
  modify @@ fun st ->
  {st with
   per_process =
     {st.per_process with env = GlobalEnv.replace_datatype dlbl desc st.per_process.env}}




let pushl e =
  modifyl (fun es -> es #< e) >>
  update_env e

let pushr e =
  modifyr (fun es -> `Entry e :: es) >>
  update_env e

let run ~per_process_opt ~mlconf (m : 'a m) : 'a  =
  let per_process = match per_process_opt with Some mem -> mem | None -> init_per_process () in
  let _, r = m Emp {per_process; lcx = Emp; resenv = ResEnv.init (); mlenv = ML.Env.init ~mlconf; rcx = []} in
  r


let isolate (m : 'a m) : 'a m =
  fun ps st ->
    let st', a = m ps {st with lcx = Emp; rcx = []} in
    {per_process = st'.per_process; mlenv = st'.mlenv; resenv = st'.resenv; lcx = st.lcx <.> st'.lcx; rcx = st'.rcx @ st.rcx}, a

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
  | Snoc (mcx, e) -> setl mcx >> ret e
  | _ ->
    dump_state Format.err_formatter "Tried to pop-left" `All >>= fun _ ->
    failwith "popl: empty"

let get_global_env =
  get >>= fun st ->
  let rec go_params =
    function
    | Emp -> st.per_process.env
    | Snoc (psi, (x, `I)) ->
      GlobalEnv.ext_dim (go_params psi) x
    | Snoc (psi, (x, `P ty)) ->
      GlobalEnv.ext (go_params psi) x @@ `P ty
    | Snoc (psi, (x, `Def (ty, tm))) ->
      GlobalEnv.define (go_params psi) x ~ty ~tm
    | Snoc (psi, (x, `Tw (ty0, ty1))) ->
      GlobalEnv.ext (go_params psi) x @@ `Tw (ty0, ty1)
    | Snoc (psi, (_, `R (r0, r1))) ->
      GlobalEnv.restrict r0 r1 (go_params psi)
    | Snoc (psi, (_, `NullaryExt)) ->
      go_params psi
  in
  ask >>= fun psi ->
  ret @@ go_params psi


let resolver =
  let rec go_locals renv =
    function
    | Emp -> renv
    | Snoc (psi, (x, _)) ->
      let renv = go_locals renv psi in
      begin
        match Name.name x with
        | Some str ->
          ResEnv.named_var `Private str x renv
        | None ->
          renv
      end
  in

  get >>= fun st ->
  ask >>= fun psi ->
  M.ret @@ go_locals st.resenv psi

let modify_top_resolver f =
  assert_top_level >>
  modify @@ fun st ->
  {st with resenv = f st.resenv}

let popr_opt =
  let rec go theta =
    getr >>= function
    | `Entry e :: rcx ->
      setr (`Update theta :: rcx) >>
      if Occurs.Set.is_empty theta then
        ret @@ Some e
      else
        get >>= fun st ->
        ret @@ Some (Entry.subst st.per_process.env e)
    | `Update theta' :: rcx ->
      setr rcx >>
      go @@ Occurs.Set.union theta theta'
    | [] ->
      ret None
  in
  go Occurs.Set.empty

let push_update x =
  modifyr @@ fun rcx ->
  `Update (Occurs.Set.singleton x) :: rcx

let popr =
  popr_opt >>= function
  | Some e -> ret e
  | None -> failwith "popr: empty"

let go_left =
  popl >>= pushr


let go_to_top =
  get >>= fun {lcx; rcx} ->
  setl Emp >>
  setr (Bwd.map (fun e -> `Entry e) lcx <>> rcx)

let in_scope x p =
  local @@ fun ps ->
  ps #< (x, p)

let in_scopes ps =
  local @@ fun ps' ->
  ps' <>< ps


let lookup_var x w =
  let rec go gm =
    match w, gm with
    | `Only, Snoc (gm, (y, `P ty)) ->
      if x = y then M.ret ty else go gm
    | `Only, Snoc (gm, (y, `Def (ty, _))) ->
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
  get >>= fun st ->
  let ty = GlobalEnv.lookup_ty st.per_process.env x `Only in
  let info = Map.find x st.per_process.info in
  ret (ty, info)


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


let base_cx =
  get_global_env >>= fun env ->
  ret @@ Cx.init env


let check ~ty ?sys:(sys = []) tm =
  base_cx >>= fun lcx ->
  let vty = Cx.eval lcx ty in
  let vsys = Cx.eval_tm_sys lcx sys in
  try
    Typing.check_ lcx vty vsys tm;
    ret `Ok
  with
  | exn ->
    ret @@ `Exn exn

let check_eq ~ty tm0 tm1 =
  if tm0 = tm1 then ret `Ok else
    base_cx >>= fun lcx ->
    let vty = Cx.eval lcx ty in
    let el0 = Cx.eval lcx tm0 in
    let el1 = Cx.eval lcx tm1 in
    try
      Cx.check_eq lcx ~ty:vty el0 el1;
      ret `Ok
    with
    | exn ->
      ret @@ `Exn exn

let check_subtype ty0 ty1 =
  base_cx >>= fun lcx ->
  let vty0 = Cx.eval lcx ty0 in
  let vty1 = Cx.eval lcx ty1 in
  try
    Cx.check_subtype lcx vty0 vty1;
    ret `Ok
  with
  | exn ->
    ret @@ `Exn exn

let compare_dim tr0 tr1 =
  base_cx >>= fun cx ->
  let r0 = Cx.eval_dim cx tr0 in
  let r1 = Cx.eval_dim cx tr1 in
  ret @@ I.compare r0 r1

let check_eq_dim tr0 tr1 =
  base_cx >>= fun cx ->
  let r0 = Cx.eval_dim cx tr0 in
  let r1 = Cx.eval_dim cx tr1 in
  match I.compare r0 r1 with
  | `Same ->
    ret true
  | _ ->
    ret false

let under_restriction r0 r1 m =
  compare_dim r0 r1 >>= function
  | `Apart ->
    ret None
  | _ ->
    get_global_env >>= fun env ->
    try
      (* TODO: hack, fix please *)
      let _ = GlobalEnv.restrict r0 r1 env in
      in_scope (Name.fresh ()) (`R (r0, r1)) m >>= fun x ->
      ret (Some x)
    with
    | I.Inconsistent ->
      ret None

let get_unsolved_holes =
  getl <<@> fun lcx ->
    Bwd.filter Entry.is_incomplete lcx


let report_unsolved ~loc =
  get_unsolved_holes <<@> Bwd.length <<@> fun n ->
    if n > 0 then
      begin
        let pp fmt () = Format.fprintf fmt "%i unsolved holes" n in
        Log.pp_message ~loc ~lvl:`Info pp Format.std_formatter ();
      end
